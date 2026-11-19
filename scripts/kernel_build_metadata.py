"""Prepare Lake 4.35 cache metadata before the first exact input fingerprint.

No package configuration, project module or dependency object is evaluated.
Only short lowercase hexadecimal sidecars in installed dependency build trees
are zero-padded. The one missing ProofWidgets lockfile sidecar is computed by
a fixed toolchain-only helper. Sources and compiled outputs remain untouched.
After preparation every sidecar remains in the complete fingerprint; build and
audit checks must not call this function or replace their original baseline.
"""
import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile

from kernel_build_environment import toolchain_inputs, stable_identity, MAX_INPUT_FILES
from kernel_build_inventory import FORBIDDEN_ENV
from kernel_build_manifest import require
from kernel_build_packages import package_environment
from kernel_build_restore import no_links

HASH_SOURCE = r"""import Lake.Build.Trace

def main (args : List String) : IO Unit := do
  match args with
  | [path] => IO.println (toString (← Lake.computeTextFileHash path))
  | _ => throw (IO.userError "one data file required")
"""


def text_hash(prefix, path):
    """Invoke only the authenticated toolchain, outside the candidate checkout."""
    prefix, path = Path(prefix).resolve(), Path(path).resolve()
    executable = prefix/'bin'/('lean.exe' if os.name == 'nt' else 'lean')
    environment = {k: os.environ[k] for k in ('SystemRoot', 'WINDIR') if k in os.environ}
    environment.update(PATH=str(prefix/'bin'), LEAN_SYSROOT=str(prefix),
                       LEAN_PATH=str(prefix/'lib/lean'))
    with tempfile.TemporaryDirectory(prefix='kernel-lake-metadata-') as temporary:
        directory = Path(temporary)
        script = directory/'Hash.lean'
        script.write_text(HASH_SOURCE, encoding='utf-8', newline='\n')
        result = subprocess.run([str(executable), '--run', str(script), str(path)],
            cwd=directory, env=environment, capture_output=True, timeout=60, check=False)
    require(result.returncode == 0 and re.fullmatch(b'[0-9a-f]{16}\r?\n', result.stdout),
            'Toolchain-only lockfile hash could not be computed')
    return result.stdout.rstrip(b'\r\n')


def rewrite_short_hash(path):
    no_links(path)
    require(path.is_file(), 'Cache sidecar is not a regular file')
    before = path.stat()
    if before.st_size >= 16:
        return None
    with path.open('rb') as stream:
        raw = stream.read(17)
    require(stable_identity(path.stat()) == stable_identity(before),
            'Cache sidecar changed while reading')
    if not re.fullmatch(b'[0-9a-f]{1,15}', raw):
        return None
    target = path.with_suffix('')
    no_links(target)
    require(target.is_file(), 'Short cache sidecar has no regular data file')
    require(before.st_nlink == 1, 'Shared cache sidecar cannot be rewritten')
    padded = raw.rjust(16, b'0')
    # Preserve the original permission bits; no cache/output is deleted.
    with path.open('r+b') as stream:
        require(stable_identity(os.fstat(stream.fileno())) == stable_identity(before),
                'Cache sidecar changed before writing')
        stream.write(padded); stream.truncate()
    return {'kind': 'zero_pad_hex', 'before_sha256': hashlib.sha256(raw).hexdigest(),
            'after_sha256': hashlib.sha256(padded).hexdigest()}


def prepare_metadata(workspace, prefix, *, expected_environment=None, environ=None,
                     git_executable='git'):
    environment = dict(os.environ if environ is None else environ)
    require(not any(environment.get(k) or os.environ.get(k) for k in FORBIDDEN_ENV),
            'Metadata preparation requires a credential-free process')
    root, prefix = Path(workspace).absolute(), Path(prefix).absolute()
    no_links(root); no_links(prefix)
    packages = package_environment(root, git_executable=git_executable)
    compiler = toolchain_inputs(prefix)['summary']
    if expected_environment is not None:
        require(expected_environment.get('packages') == packages and
                expected_environment.get('toolchain') == compiler,
                'Metadata preparation compiler or package identity differs from producer')
    changes, examined = [], 0
    for name, package in packages['packages'].items():
        if package['type'] != 'git':
            continue
        directory = root/package['location']
        build = directory/'.lake/build'
        if build.exists():
            no_links(build)
            def failed(error):
                raise ValueError('Could not enumerate dependency cache metadata') from error
            for current, dirs, files in os.walk(build, followlinks=False, onerror=failed):
                for item in dirs:
                    no_links(Path(current)/item)
                for item in files:
                    examined += 1
                    require(examined <= MAX_INPUT_FILES, 'Cache metadata file limit exceeded')
                    if not item.endswith('.hash'):
                        continue
                    path = Path(current)/item
                    change = rewrite_short_hash(path)
                    if change:
                        changes.append({'package': name, 'path': path.relative_to(directory).as_posix(), **change})
        # This target is a text file in the pinned ProofWidgets Lake recipe.
        # It can create its .hash during a no-build traversal despite cache get.
        if name == 'proofwidgets' and package.get('subdirectory') is None:
            lock = directory/'widget/package-lock.json'
            sidecar = lock.with_name(lock.name+'.hash')
            no_links(lock); no_links(sidecar)
            if lock.exists() and not sidecar.exists():
                require(lock.is_file() and lock.stat().st_size <= 16*1024*1024,
                        'Unsupported ProofWidgets lockfile')
                before = lock.stat()
                value = text_hash(prefix, lock)
                require(stable_identity(lock.stat()) == stable_identity(before),
                        'ProofWidgets lockfile changed while hashing')
                with sidecar.open('xb') as stream:
                    stream.write(value)
                changes.append({'package': name, 'path': sidecar.relative_to(directory).as_posix(),
                                'kind': 'missing_text_hash', 'after_sha256': hashlib.sha256(value).hexdigest()})
    require(toolchain_inputs(prefix)['summary'] == compiler,
            'Toolchain changed during metadata preparation')
    return {'schema': 'kernel-cache-metadata/v1', 'changes': changes,
            'sources_or_objects_written': False, 'candidate_code_executed': False}
