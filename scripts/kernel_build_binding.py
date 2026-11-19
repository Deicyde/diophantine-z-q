"""Bind observed Lean imports to the already fingerprinted input inventories.

This consumes actual --deps/--src-deps results, not guessed module filenames.
It does not authenticate the inventories or run code. The workflow must first
verify producer provenance and collect installed inputs without credentials.
Project source lookup is checked before restoration; compiled project lookup
can additionally be checked by the producer after its cold build.
"""
import os
from pathlib import PurePosixPath

from kernel_build_layout import NAME
from kernel_build_manifest import digest, regular_path, require


def observed(row):
    require(isinstance(row, dict) and row.get('owner') in {'workspace', 'toolchain'}
            and regular_path(row.get('path')) and digest(row.get('sha256'))
            and type(row.get('size')) is int and row['size'] >= 0,
            'Malformed resolved input record')
    return row


def matches(row, files, relative):
    expected = files.get(relative)
    require(isinstance(expected, dict) and expected.get('sha256') == row['sha256']
            and expected.get('size') == row['size'],
            'Resolved input differs from the fingerprinted installation')


def bind_project_lookups(lookups, project_paths):
    """Check actual source lookup against every contract-owned project module."""
    require(isinstance(lookups, dict) and isinstance(project_paths, dict)
            and bool(project_paths) and set(lookups) == set(project_paths),
            'Project lookup does not cover the exact contract inventory')
    seen = set()
    for name, paths in project_paths.items():
        require(isinstance(name, str) and NAME.fullmatch(name) and isinstance(paths, dict),
                'Malformed project path binding')
        row = lookups[name]
        require(isinstance(row, dict) and set(row) in ({'source'}, {'source', 'compiled'}),
                'Missing or unsupported project lookup')
        source = observed(row['source'])
        require(source['owner'] == 'workspace' and source['path'] == paths.get('source_path'),
                'Actual project source lookup differs from the contract layout')
        require(source['path'].casefold() not in seen, 'Aliased project source lookup')
        seen.add(source['path'].casefold())
        if 'compiled' in row:
            compiled = observed(row['compiled'])
            require(compiled['owner'] == 'workspace'
                    and compiled['path'] == paths.get('lean_output_prefix', '') + '.olean',
                    'Actual project compiled lookup differs from the contract layout')
    # Output bytes belong in module/producer output records, not the shared
    # environment: putting them here would invalidate all reuse on one edit.
    return {name: dict(paths) for name, paths in project_paths.items()}


def bind_external_lookups(lookups, packages, compiler, dependency_files):
    """Return collector-compatible external/builtin rows with actual identities.

    Both source and compiled forms of an external module must belong to the
    same installed pinned package. A workspace shadow, mixed package, changed
    object or unrecorded file is never accepted on the basis of its name.
    """
    require(isinstance(lookups, dict) and isinstance(packages, dict)
            and isinstance(packages.get('packages'), dict)
            and isinstance(compiler, dict) and isinstance(compiler.get('files'), dict)
            and isinstance(compiler.get('builtins'), dict)
            and isinstance(dependency_files, dict), 'Missing installed input inventories')
    external, builtin, seen_names = {}, {}, set()
    seen_inputs = {'source': set(), 'compiled': set()}
    for name, row in lookups.items():
        require(isinstance(name, str) and NAME.fullmatch(name) and name.casefold() not in seen_names,
                'Invalid or aliased external module name')
        seen_names.add(name.casefold())
        require(isinstance(row, dict) and set(row) == {'source', 'compiled'},
                'External lookup requires both source and compiled identities')
        source, compiled = observed(row['source']), observed(row['compiled'])
        for kind, record in row.items():
            identity = record['owner'], record['path'].casefold()
            require(identity not in seen_inputs[kind], 'Aliased external input path')
            seen_inputs[kind].add(identity)
        require(source['owner'] == compiled['owner'], 'Source and compiled import have different owners')
        if compiled['owner'] == 'toolchain':
            expected = compiler['builtins'].get(name)
            require(isinstance(expected, dict)
                    and expected.get('compiled_path') == compiled['path']
                    and expected.get('compiled_sha256') == compiled['sha256'],
                    'Actual builtin lookup differs from the installed compiler')
            matches(compiled, compiler['files'], compiled['path'])
            builtin[name] = {'compiled_path': compiled['path'], 'compiled_sha256': compiled['sha256'],
                             'source_path': source['path'], 'source_sha256': source['sha256']}
            continue
        owners = []
        for package, entry in packages['packages'].items():
            if not isinstance(entry, dict) or entry.get('type') != 'git':
                continue
            location = entry.get('location')
            require(regular_path(location), 'Invalid installed package location')
            root = PurePosixPath(location)
            if all(PurePosixPath(item['path']).is_relative_to(root) for item in (source, compiled)):
                owners.append((package, entry, root))
        require(len(owners) == 1, 'External source/object are not in one unique pinned package')
        package, entry, root = owners[0]
        require(isinstance(entry.get('revision'), str) and bool(entry['revision']), 'Missing package revision')
        files = dependency_files.get(package)
        require(isinstance(files, dict), 'Installed dependency fingerprint is missing')
        for item in (source, compiled):
            matches(item, files, PurePosixPath(item['path']).relative_to(root).as_posix())
        external[name] = {'package': package, 'revision': entry['revision'],
                          'source_path': source['path'], 'source_sha256': source['sha256'],
                          'compiled_path': compiled['path'], 'compiled_sha256': compiled['sha256']}
    return external, builtin


def collect_bound_inventory(root, prefix, module_paths, packages, compiler,
                            dependency_files, lake_environment):
    """Connect header parsing, actual lookup, installed identities and closure.

    This is the credential-free collection stage. The caller has already
    authenticated and checked the installed compiler/package fingerprints
    before obtaining lake_environment. This function does not build or restore
    any project output. Current project objects need not exist. The second
    return value is detailed evidence, not a shared environment identity:
    source/import identities already enter each module's inputs. Only the
    common project layout belongs in that shared identity, or adding an
    independent module would unnecessarily invalidate every cached module.
    """
    from pathlib import Path
    from kernel_build_inventory import collect, query_headers, read_source
    from kernel_build_layout import bind_project_paths, project_layout
    from kernel_build_resolution import resolve_imports

    root, prefix = Path(root).absolute(), Path(prefix).absolute()
    layout = project_layout(root)
    paths = bind_project_paths(root, module_paths, layout)
    before = {name: read_source(root, path) for name, path in module_paths.items()}
    rows = {}
    names = sorted(module_paths)
    lean = prefix/'bin'/('lean.exe' if os.name == 'nt' else 'lean')
    for start in range(0, len(names), 64):
        batch = {name: module_paths[name] for name in names[start:start+64]}
        rows.update(query_headers(root, batch, lean=str(lean)))
    project_lookups = resolve_imports(root, prefix, names, lake_environment, kinds=('source',))
    binding = bind_project_lookups(project_lookups, paths)
    require(all(project_lookups[name]['source']['sha256'] == before[name] for name in names),
            'Project source changed while parsing headers or resolving imports')
    external_names = sorted({name for row in rows.values() for name in row['imports']} - set(names))
    external_lookups = resolve_imports(root, prefix, external_names, lake_environment) if external_names else {}
    external, builtin = bind_external_lookups(external_lookups, packages, compiler, dependency_files)
    inventory = collect(root, module_paths, external, builtin,
                        query=lambda _root, batch: {name: rows[name] for name in batch})
    require(all(inventory[name]['inputs']['source_sha256'] == before[name] for name in names),
            'Project source changed during bound inventory collection')
    require(project_layout(root) == layout, 'Project layout changed during bound inventory collection')
    return inventory, {'project_layout': layout, 'project_resolution': binding,
                       'external_resolution': external, 'builtin_resolution': builtin}
