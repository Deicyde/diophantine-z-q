"""Fingerprint actual compiler and dependency files before main-output reuse.

No Lake configuration is evaluated, no dependency is fetched, and no candidate
code is executed. Call from the trusted preparation code before candidate
execution. The caller still has to bind the build commands and actual module
resolution; a toolchain version string or dependency commit alone is not enough.
"""
import hashlib
import json
import os
from pathlib import Path
import platform
import stat

from kernel_build_manifest import regular_path, require
from kernel_build_packages import file_record, package_environment
from kernel_build_restore import no_links

MAX_INPUT_FILES = 250000
MAX_INPUT_BYTES = 64 * 1024 ** 3
BUILD_ENVIRONMENT_KEYS = (
    'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LEAN_OPTS', 'LEAN_NUM_THREADS',
    'LAKE_NO_CACHE', 'LAKE_ARTIFACT_CACHE', 'LAKE_CACHE_DIR', 'LAKE_EXTRA_ARGS',
    'CC', 'CXX', 'AR', 'CFLAGS', 'CPPFLAGS', 'CXXFLAGS', 'LDFLAGS',
    'LD_PRELOAD', 'LD_LIBRARY_PATH', 'DYLD_INSERT_LIBRARIES', 'DYLD_LIBRARY_PATH',
    'LEAN', 'LAKE', 'LAKE_HOME', 'LAKE_OVERRIDE_LEAN', 'LEAN_GITHASH', 'LEAN_CC', 'LEAN_AR',
    'ELAN_TOOLCHAIN', 'LAKE_CONFIG', 'LAKE_RESTORE_ARTIFACTS', 'LAKE_PKG_URL_MAP',
)


def stable_identity(info, *, include_mode=True):
    fields = info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns
    return (*fields, stat.S_IMODE(info.st_mode)) if include_mode else fields


def file_fingerprint(root, path, *, maximum_bytes=None):
    """Accept a file link only when its resolved target stays in this input root."""
    before_link = path.lstat()
    resolved = path.resolve(strict=True)
    require(resolved.is_relative_to(root) and resolved.is_file(),
            'Input file resolves outside its approved root')
    require(stat.S_ISREG(before_link.st_mode) or stat.S_ISLNK(before_link.st_mode),
            'Input is not a regular file or internal file link')
    before = resolved.stat()
    require(stat.S_ISREG(before.st_mode), 'Input target is not a regular file')
    require(0 <= before.st_size <= (MAX_INPUT_BYTES if maximum_bytes is None else maximum_bytes),
            'Input inventory exceeds byte limit')
    with resolved.open('rb') as stream:
        # Windows path stat adds execute bits from the .exe suffix; fstat has
        # no filename and omits those bits. Compare file identity here, then
        # compare path modes using path stat on both sides below.
        require(stable_identity(os.fstat(stream.fileno()), include_mode=False) ==
                stable_identity(before, include_mode=False),
                'Input changed before hashing')
        digest = hashlib.file_digest(stream, 'sha256').hexdigest()
        require(stable_identity(os.fstat(stream.fileno()), include_mode=False) ==
                stable_identity(before, include_mode=False),
                'Input changed while hashing')
    require(stable_identity(resolved.stat()) == stable_identity(before) and
            stable_identity(path.lstat()) == stable_identity(before_link) and
            path.resolve(strict=True) == resolved, 'Input changed after hashing')
    row = {'sha256': digest, 'size': before.st_size, 'mode': stat.S_IMODE(before.st_mode)}
    if stat.S_ISLNK(before_link.st_mode):
        row['link_target'] = resolved.relative_to(root).as_posix()
    return row


def fingerprint_tree(root, roots=('.',), *, skip_git=False):
    """Hash every file in explicit roots; refuse directory links and aliases.

    File lists and permissions, as well as contents, affect the result. Paths
    are relative so identical installations at different host paths can match.
    Only Git metadata may be excluded. Build outputs are never excluded.
    """
    root = Path(root).absolute()
    no_links(root)
    require(root.is_dir(), 'Missing compiler or dependency input root')
    resolved_root = root.resolve()
    require(isinstance(roots, (tuple, list)) and bool(roots) and len(set(roots)) == len(roots),
            'Missing or duplicate fingerprint roots')
    records, folded, total = {}, set(), 0
    for relative in roots:
        require(relative == '.' or regular_path(relative), 'Unsafe fingerprint root')
        start = root / relative
        no_links(start)
        require(start.is_dir(), 'Missing fingerprint directory')
        def traversal_error(error):
            raise ValueError('Input directory could not be completely enumerated') from error
        for directory, dirs, files in os.walk(start, followlinks=False, onerror=traversal_error):
            current = Path(directory)
            for name in list(dirs):
                child = current/name
                if skip_git and name == '.git':
                    dirs.remove(name)
                    continue
                require(not child.is_symlink() and not getattr(child, 'is_junction', lambda: False)(),
                        'Directory links cannot supply reusable inputs')
            for name in sorted(files):
                if skip_git and name == '.git':
                    continue
                child = current/name
                path = child.relative_to(root).as_posix()
                require(regular_path(path) and path.casefold() not in folded,
                        'Duplicate or aliased input path')
                folded.add(path.casefold())
                require(len(folded) <= MAX_INPUT_FILES, 'Input inventory exceeds file limit')
                records[path] = file_fingerprint(resolved_root, child, maximum_bytes=MAX_INPUT_BYTES-total)
                total += records[path]['size']
                require(total <= MAX_INPUT_BYTES, 'Input inventory exceeds byte limit')
    require(bool(records), 'Empty input inventory')
    canonical = json.dumps(records, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()
    return {'sha256': hashlib.sha256(canonical).hexdigest(), 'files': len(records),
            'bytes': total}, records


def toolchain_inputs(prefix):
    """Bind the shipped executables, libraries, headers and support files."""
    prefix = Path(prefix).absolute()
    roots = ['bin', 'include', 'lib']
    if (prefix/'share').exists():
        roots.append('share')
    summary, records = fingerprint_tree(prefix, roots)
    builtins = {}
    for path, row in records.items():
        if path.startswith('lib/lean/') and path.endswith('.olean'):
            name = path[len('lib/lean/'):-len('.olean')].replace('/', '.')
            builtins[name] = {'compiled_path': path, 'compiled_sha256': row['sha256']}
    require(bool(builtins) and any(path in records for path in ('bin/lean', 'bin/lean.exe'))
            and any(path in records for path in ('bin/lake', 'bin/lake.exe')),
            'Incomplete Lean toolchain')
    return {'summary': summary, 'builtins': builtins, 'files': records}


def dependency_inputs(root, packages):
    """Bind installed dependency sources AND compiled/cache files, not just Git HEAD.

    Local project packages are covered by project source/output inventories;
    their configuration is already bound by package_environment. This does
    not assume that an untracked .olean came from the pinned source commit.
    """
    result, detail = {}, {}
    for name, package in packages['packages'].items():
        if package['type'] != 'git':
            continue
        summary, files = fingerprint_tree(Path(root)/package['location'], skip_git=True)
        result[name] = {'revision': package['revision'], **summary}
        detail[name] = files
    return result, detail


def collect_environment(root, prefix, build_commands, source_resolution, *,
                        driver_paths, git_executable='git', environ=None, controls=None):
    """Collect portable facts; caller binds resolution to actual compiler lookup.

    Keep the detailed records in an artifact. Only their complete hashes enter
    the compact bundle environment. Commands, driver bytes, source resolution,
    external runtime selection and environment overrides all affect equality.
    This does not authorize reuse on its own: authenticated producer selection,
    source equality, closure checks and archive verification remain required.
    """
    environ = os.environ if environ is None else environ
    require(isinstance(build_commands, list) and bool(build_commands) and all(
        isinstance(command, list) and command and all(isinstance(x, str) for x in command)
        for command in build_commands), 'Missing actual build commands')
    require(isinstance(source_resolution, dict) and bool(source_resolution),
            'Missing actual module source resolution')
    require(isinstance(driver_paths, (list, tuple)) and bool(driver_paths), 'Missing build driver inventory')
    packages = package_environment(root, git_executable=git_executable)
    compiler = toolchain_inputs(prefix)
    dependencies, dependency_files = dependency_inputs(root, packages)
    drivers = {path: file_record(Path(root), path)[0] for path in driver_paths}
    overrides = {key: environ.get(key) for key in BUILD_ENVIRONMENT_KEYS}
    controls_record = None
    if controls is not None:
        from kernel_build_controls import verify_controls
        controls_record = verify_controls(root, controls, environ)
        # The fresh directory differs on every runner. Substitute only these
        # two verified paths; all effective settings and file bytes stay bound.
        overrides['LAKE_CONFIG'] = '@verified-controls/lake-config.toml'
        overrides['LAKE_CACHE_DIR'] = '@verified-controls/cache'
    environment = {
        'schema': 'kernel-build-environment/v1', 'packages': packages,
        'dependency_inputs': dependencies, 'toolchain': compiler['summary'],
        'commands': build_commands, 'drivers': drivers, 'source_resolution': source_resolution,
        'platform': {'system': platform.system(), 'machine': platform.machine(),
                     'libc': list(platform.libc_ver()), 'runner_image': environ.get('ImageOS'),
                     'runner_image_version': environ.get('ImageVersion')},
        'environment_overrides': overrides,
    }
    if controls_record is not None:
        environment['lake_controls'] = controls_record
    return environment, {'toolchain_files': compiler['files'], 'builtins': compiler['builtins'],
                         'dependency_files': dependency_files}
