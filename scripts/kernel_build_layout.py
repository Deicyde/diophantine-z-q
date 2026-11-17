"""Check project module paths against a deliberately narrow Lake TOML subset.

Lean 4.35 resolves a default-glob library's root and submodules at
package.srcDir / library.srcDir / module-name. See Lake/Config/Module.lean,
LeanLib.lean and LeanLibConfig.lean in that toolchain. Ambiguous ownership,
custom globs, executable configuration and unsupported options select no
reuse. This checks project layout only, not external import search order.
"""
from pathlib import Path, PurePosixPath
import re
import tomllib

from kernel_build_manifest import regular_path, require, unique_json
from kernel_build_packages import file_record
from kernel_build_restore import no_links

PACKAGE_FIELDS = {'name', 'version', 'defaultTargets', 'requiresModuleSystem',
                  'require', 'lean_lib', 'srcDir', 'buildDir', 'leanLibDir',
                  'irDir', 'leanOptions'}
LIBRARY_FIELDS = {'name', 'srcDir', 'roots', 'leanOptions'}
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def subpath(*parts):
    require(all(isinstance(p, str) and (p == '.' or regular_path(p)) for p in parts),
            'Unsafe Lake layout directory')
    result = PurePosixPath(*parts).as_posix()
    require(result == '.' or regular_path(result), 'Invalid Lake layout path')
    return result


def project_layout(root):
    root = Path(root).absolute()
    no_links(root)
    manifest_record, raw = file_record(root, 'lake-manifest.json')
    manifest = unique_json(raw)
    require(isinstance(manifest, dict) and isinstance(manifest.get('packages'), list),
            'Missing package manifest for project layout')
    locations = ['.']
    for entry in manifest['packages']:
        require(isinstance(entry, dict) and entry.get('type') in {'path', 'git'},
                'Unknown workspace package kind')
        if entry['type'] != 'path':
            continue
        location = entry.get('dir')
        if isinstance(location, str) and location.startswith('./'):
            location = location[2:]
        require(regular_path(location) and entry.get('configFile') == 'lakefile.toml',
                'Local package requires unsupported or unsafe configuration')
        locations.append(location)
    require(len({p.casefold() for p in locations}) == len(locations), 'Duplicate local package location')
    configs, libraries, names = {}, [], set()
    for location in locations:
        require(not (root/location/'lakefile.lean').exists(),
                'Executable Lake configuration does not qualify for static layout reuse')
        config_path = subpath(location, 'lakefile.toml')
        record, raw = file_record(root, config_path)
        value = tomllib.loads(raw.decode('utf-8'))
        require(set(value) <= PACKAGE_FIELDS, 'Unsupported package layout or build option')
        package_name = value.get('name')
        require(isinstance(package_name, str) and NAME.fullmatch(package_name)
                and package_name not in names, 'Invalid or duplicate project package name')
        names.add(package_name)
        configs[config_path] = record
        source_root = subpath(location, value.get('srcDir', '.'))
        build_root = subpath(location, value.get('buildDir', '.lake/build'))
        lean_root = subpath(build_root, value.get('leanLibDir', 'lib/lean'))
        ir_root = subpath(build_root, value.get('irDir', 'ir'))
        rows = value.get('lean_lib')
        require(isinstance(rows, list) and bool(rows), 'Missing project Lean libraries')
        lib_names = set()
        for lib in rows:
            require(isinstance(lib, dict) and set(lib) <= LIBRARY_FIELDS,
                    'Unsupported library layout; custom globs cannot supply reuse')
            name = lib.get('name')
            require(isinstance(name, str) and NAME.fullmatch(name) and name not in lib_names,
                    'Invalid or duplicate library name')
            lib_names.add(name)
            roots = lib.get('roots', [name])
            require(isinstance(roots, list) and bool(roots) and all(isinstance(n, str)
                    and NAME.fullmatch(n) for n in roots) and len(set(roots)) == len(roots),
                    'Invalid library module roots')
            libraries.append({'package': package_name, 'library': name, 'roots': roots,
                              'source_root': subpath(source_root, lib.get('srcDir', '.')),
                              'lean_output_root': lean_root, 'ir_output_root': ir_root})
    return {'schema': 'kernel-project-layout/v1', 'manifest': manifest_record,
            'configs': configs, 'libraries': libraries}


def bind_project_paths(root, module_paths, layout):
    """Return each module's unique source and output owner or reject reuse."""
    root = Path(root).absolute()
    require(isinstance(module_paths, dict) and bool(module_paths), 'Missing contract module paths')
    require(isinstance(layout, dict) and layout.get('schema') == 'kernel-project-layout/v1',
            'Unsupported project layout')
    # Re-read the config bytes so an earlier layout is not silently used after an edit.
    require(project_layout(root) == layout, 'Project layout changed during collection')
    require(all(isinstance(n, str) and NAME.fullmatch(n) for n in module_paths), 'Unsupported module name')
    require(len({n.casefold() for n in module_paths}) == len(module_paths), 'Case-aliased project modules')
    result = {}
    for name, path in module_paths.items():
        require(regular_path(path) and path.endswith('.lean'), 'Invalid project source path')
        owners = [lib for lib in layout['libraries'] if any(
            name == prefix or name.startswith(prefix+'.') for prefix in lib['roots'])]
        require(len(owners) == 1, 'Project module has missing or ambiguous library ownership')
        owner = owners[0]
        relative = name.replace('.', '/')
        expected = subpath(owner['source_root'], relative+'.lean')
        require(path == expected, 'Contract source differs from Lake module resolution')
        source = root/path
        no_links(source)
        require(source.is_file() and source.resolve().is_relative_to(root.resolve()),
                'Resolved project source is not an ordinary workspace file')
        result[name] = {'package': owner['package'], 'library': owner['library'], 'source_path': path,
                        'lean_output_prefix': subpath(owner['lean_output_root'], relative),
                        'ir_output_prefix': subpath(owner['ir_output_root'], relative)}
    return result
