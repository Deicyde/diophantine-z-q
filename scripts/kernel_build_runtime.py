"""Bind the Linux loader's selected libraries for already verified build tools.

Call only from trusted preparation code, after compiler/dependency fingerprints
match. Never pass candidate executables. The collector examines every ELF file
in those verified native input roots, not merely `lean --version`, and the
explicit system driver list. It performs no compilation or project import.
The same library-search environment must be used for the subsequent build.
This is runtime evidence, not producer authentication or audit acceptance.
"""
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess

from kernel_build_environment import file_fingerprint
from kernel_build_inventory import FORBIDDEN_ENV
from kernel_build_manifest import require


MAX_ELF_FILES = 10000
MAX_LOADER_OUTPUT = 1024 * 1024
LOADER_OVERRIDES = ('LD_PRELOAD', 'LD_AUDIT', 'LD_ASSUME_KERNEL', 'LD_HWCAP_MASK',
                    'LD_ORIGIN_PATH', 'GLIBC_TUNABLES', 'LD_PROFILE', 'LD_DEBUG',
                    'LD_DEBUG_OUTPUT', 'LD_TRACE_LOADED_OBJECTS')


def parse_ldd(output, returncode):
    """Fail closed for unresolved, truncated, or unknown loader output."""
    require(isinstance(output, str) and len(output) <= MAX_LOADER_OUTPUT,
            'Missing or oversized loader output')
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    if lines in (['statically linked'], ['not a dynamic executable']):
        require(returncode in (0, 1), 'Loader failed on a static object')
        return []
    require(returncode == 0 and bool(lines), 'Runtime library lookup failed')
    paths = set()
    for line in lines:
        if re.fullmatch(r'linux-(?:vdso|gate)\.so\.\d+ \(0x[0-9a-fA-F]+\)', line):
            continue  # Supplied by the recorded host kernel, not a filesystem file.
        match = re.fullmatch(r'(?:[^\s]+ => )?(/[^\r\n]+) \(0x[0-9a-fA-F]+\)', line)
        require(match is not None, 'Unresolved or unrecognized runtime library')
        path = match.group(1)
        require('\x00' not in path and Path(path).is_absolute(), 'Invalid runtime library path')
        paths.add(path)
    require(bool(paths), 'Loader reported no filesystem runtime')
    return sorted(paths)


def native_inputs(verified_roots):
    """Select ELF files only from exact, already authenticated file inventories."""
    require(isinstance(verified_roots, dict) and bool(verified_roots),
            'Missing verified native input roots')
    result = []
    for root, files in verified_roots.items():
        root = Path(root).resolve(strict=True)
        require(root.is_dir() and isinstance(files, dict) and bool(files),
                'Invalid verified native input root')
        for relative, expected in files.items():
            path = root/relative
            require(path.resolve(strict=True).is_relative_to(root),
                    'Native input escaped its verified root')
            with path.open('rb') as stream:
                elf = stream.read(4) == b'\x7fELF'
            if not elf:
                continue
            require(file_fingerprint(root, path) == expected,
                    'Native input changed since fingerprinting')
            result.append(path)
            require(len(result) <= MAX_ELF_FILES, 'Native runtime inventory exceeds limit')
    require(bool(result), 'No verified ELF tools or libraries')
    return result


def capture_runtime(verified_roots, system_drivers, *, environ=None, ldd='/usr/bin/ldd'):
    """Capture actual transitive loader paths, hashes, and host ABI identity.

    system_drivers must be the trusted workflow's absolute executable paths,
    including its Python, shell and Git. Host paths are deliberately retained:
    different installed layouts select a cold build. Detailed loader records
    belong in the evidence artifact; their digest enters the reuse identity.
    A caller must compare this identity again after the full build and audit.
    """
    require(platform.system() == 'Linux', 'Runtime capture currently requires Linux')
    environment = dict(os.environ if environ is None else environ)
    require(not any(environment.get(key) for key in (*FORBIDDEN_ENV, *LOADER_OVERRIDES)),
            'Credentials or unsupported loader override in runtime capture')
    require(isinstance(system_drivers, (list, tuple)) and bool(system_drivers)
            and all(isinstance(p, str) and Path(p).is_absolute() for p in system_drivers),
            'Missing exact system driver paths')
    require(ldd == '/usr/bin/ldd', 'Use the trusted system loader inspector')
    # ldd is a shell script on Ubuntu. Use a fixed utility PATH and locale,
    # preserving the exact dynamic-library path that will be used in the build.
    query_env = {'PATH': '/usr/bin:/bin', 'LC_ALL': 'C'}
    if environment.get('LD_LIBRARY_PATH') is not None:
        query_env['LD_LIBRARY_PATH'] = environment['LD_LIBRARY_PATH']
    preload = Path('/etc/ld.so.preload')
    require(not preload.exists() or not preload.read_bytes().strip(),
            'Host-wide loader preloading is not eligible for reuse')
    inputs = native_inputs(verified_roots)
    system_paths = [Path(p) for p in [ldd, *system_drivers]]
    for path in system_paths:
        require(path.is_file(), 'Missing runtime driver')
        with path.open('rb') as stream:
            if stream.read(4) == b'\x7fELF':
                inputs.append(path)
    inputs = sorted(set(inputs), key=str)
    require(len(inputs) <= MAX_ELF_FILES, 'Runtime tool count exceeds limit')
    # Ubuntu's loader configuration chooses the system paths. Bind both the
    # selected libraries and the cache that selected them, including absence.
    config_paths = [Path('/etc/ld.so.cache'), preload, Path('/etc/os-release')]
    files = {}
    for path in [*system_paths, *config_paths]:
        files[str(path)] = file_fingerprint(Path('/'), path) if path.exists() else None
    selected = {}
    for path in inputs:
        before = file_fingerprint(Path('/'), path)
        process = subprocess.run([ldd, str(path)], env=query_env, capture_output=True,
                                 timeout=30, check=False)
        raw = process.stdout + process.stderr
        require(len(raw) <= MAX_LOADER_OUTPUT, 'Oversized loader response')
        libraries = parse_ldd(raw.decode('utf-8'), process.returncode)
        require(file_fingerprint(Path('/'), path) == before, 'Native input changed during lookup')
        files[str(path)] = before
        selected[str(path)] = libraries
        for library in libraries:
            observed = file_fingerprint(Path('/'), Path(library))
            require(library not in files or files[library] == observed,
                    'Runtime library changed during capture')
            files[library] = observed
    for name, expected in files.items():
        path = Path(name)
        require((file_fingerprint(Path('/'), path) if path.exists() else None) == expected,
                'Runtime input changed during capture')
    evidence = {'files': files, 'selected': selected}
    identity = {'schema': 'kernel-linux-runtime/v1', 'system': platform.system(),
                'machine': platform.machine(), 'kernel': platform.release(),
                'library_search_path': environment.get('LD_LIBRARY_PATH'),
                'sha256': hashlib.sha256(json.dumps(evidence, sort_keys=True,
                    separators=(',', ':')).encode()).hexdigest(),
                'elf_files': len(inputs), 'runtime_paths': len(files)}
    return identity, evidence
