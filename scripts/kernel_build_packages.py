"""Fingerprint Lake configuration and verify the installed dependency commits.

This is one part of the reuse environment, not its complete compiler/platform
identity. It runs in the credential-free build phase and never fetches or
updates a package. A missing or dirty dependency selects a cold build or stops
the existing dependency check; it cannot authorize reuse.
"""
import hashlib
from pathlib import Path
import re
import subprocess

from kernel_build_manifest import regular_path, require, unique_json
from kernel_build_restore import no_links


def file_record(root, relative):
    require(regular_path(relative), 'Unsafe package configuration path')
    path = root / relative
    no_links(path)
    require(path.is_file() and path.resolve().is_relative_to(root.resolve()),
            'Missing package configuration')
    raw = path.read_bytes()
    return {'path': relative, 'sha256': hashlib.sha256(raw).hexdigest()}, raw


def git(root, *args, executable='git'):
    result = subprocess.run([executable, '-c', 'safe.directory='+str(root), '-C', str(root), *args],
                            capture_output=True, timeout=60)
    require(result.returncode == 0, 'Dependency Git identity unavailable')
    return result.stdout


def package_environment(root, *, git_executable='git'):
    root = Path(root).absolute()
    no_links(root)
    manifest_record, raw = file_record(root, 'lake-manifest.json')
    manifest = unique_json(raw)
    require(isinstance(manifest, dict) and isinstance(manifest.get('packages'), list)
            and regular_path(manifest.get('packagesDir')), 'Malformed Lake package manifest')
    configs = {'lake-manifest.json': manifest_record,
               'lean-toolchain': file_record(root, 'lean-toolchain')[0]}
    root_configs = [name for name in ('lakefile.toml', 'lakefile.lean') if (root/name).exists()]
    require(len(root_configs) == 1, 'Missing or ambiguous root Lake configuration')
    configs[root_configs[0]] = file_record(root, root_configs[0])[0]
    packages = {}
    for package in manifest['packages']:
        require(isinstance(package, dict) and isinstance(package.get('name'), str)
                and re.fullmatch(r'[A-Za-z0-9_-]+', package['name'])
                and package['name'] not in packages, 'Malformed or duplicate package name')
        name = package['name']
        config = package.get('configFile')
        require(config in ('lakefile.toml', 'lakefile.lean'), 'Unknown package config format')
        require(package.get('manifestFile') == 'lake-manifest.json', 'Unknown package manifest format')
        if package.get('type') == 'git':
            revision = package.get('rev')
            require(isinstance(revision, str) and re.fullmatch(r'[0-9a-f]{40}', revision),
                    'Dependency revision is not an exact commit')
            require(isinstance(package.get('url'), str) and bool(package['url']),
                    'Missing dependency repository')
            location = manifest['packagesDir'] + '/' + name
            directory = root/location
            no_links(directory)
            require(directory.is_dir(), 'Missing installed dependency')
            actual_root = Path(git(directory, 'rev-parse', '--show-toplevel',
                                   executable=git_executable).decode().strip())
            require(actual_root.resolve() == directory.resolve(),
                    'Dependency Git worktree differs from the installed package')
            require(git(directory, 'rev-parse', 'HEAD', executable=git_executable).decode().strip() == revision,
                    'Installed dependency revision differs from its pin')
            require(not git(directory, 'status', '--porcelain', '--untracked-files=no',
                            executable=git_executable).strip(), 'Modified dependency source')
            subdir = package.get('subDir')
            require(subdir is None or regular_path(subdir), 'Unsafe dependency subdirectory')
            package_dir = location if subdir is None else location + '/' + subdir
            config_record = file_record(root, package_dir+'/'+config)[0]
            # The package configuration itself must be a tracked file, not an
            # untracked shadow of a missing configuration at the pinned commit.
            config_relative = config if subdir is None else subdir+'/'+config
            git(directory, 'ls-files', '--error-unmatch', '--', config_relative,
                executable=git_executable)
            packages[name] = {'type': 'git', 'url': package['url'], 'revision': revision,
                              'location': location, 'subdirectory': subdir,
                              'config': config_record}
        elif package.get('type') == 'path':
            location = package.get('dir')
            if isinstance(location, str) and location.startswith('./'):
                location = location[2:]
            require(regular_path(location), 'Local package escapes the project')
            require(not location.startswith(manifest['packagesDir']+'/'),
                    'Local package overlaps installed dependencies')
            config_record = file_record(root, location+'/'+config)[0]
            local_manifest = file_record(root, location+'/lake-manifest.json')[0]
            packages[name] = {'type': 'path', 'location': location, 'config': config_record,
                              'manifest': local_manifest}
        else:
            raise ValueError('Unknown Lake dependency kind')
    return {'schema': 'kernel-package-environment/v1', 'configuration': configs,
            'packages': packages}
