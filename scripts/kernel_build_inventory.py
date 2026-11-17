"""Bind project source paths to the pinned compiler's parsed import inventory.

The workflow must separately validate the package/config/compiler environment
and supply the resolved external-module identities. This collector never
guesses imports from source text, downloads packages, or builds a module.
"""
import hashlib
import os
from pathlib import Path
import subprocess

from kernel_build_manifest import digest, regular_path, require, unique_json, validate_inventory
from kernel_build_restore import no_links

FORBIDDEN_ENV = ('GH_TOKEN', 'GITHUB_TOKEN', 'OPENAI_API_KEY', 'ANTHROPIC_API_KEY',
                 'ACTIONS_RUNTIME_TOKEN', 'ACTIONS_ID_TOKEN_REQUEST_TOKEN')


def read_source(root, relative):
    require(regular_path(relative) and relative.endswith('.lean'), 'Invalid source path')
    path = root / relative
    no_links(path)
    require(path.is_file() and path.resolve().is_relative_to(root.resolve()),
            'Source is missing or outside the workspace')
    return hashlib.sha256(path.read_bytes()).hexdigest()


def query_headers(root, names, *, lake='lake'):
    """Run only Lake's source/header facets, with automatic artifact reuse off.

    Evaluating a Lake configuration can itself run code. Consequently callers
    must use a credential-free build job and persist-credentials:false checkout;
    removing a token from this environment alone is not an execution sandbox.
    """
    require(not any(os.environ.get(key) for key in FORBIDDEN_ENV),
            'Source collection must run without API or artifact credentials')
    targets = [f'+{name}:{facet}' for name in names for facet in ('lean', 'imports', 'header')]
    env = dict(os.environ, LAKE_NO_CACHE='true', LAKE_ARTIFACT_CACHE='false', LAKE_CACHE_DIR='')
    result = subprocess.run([lake, '-J', 'query', *targets], cwd=root, env=env,
                            capture_output=True, timeout=120, check=False)
    require(result.returncode == 0, 'Compiler source/header query failed')
    require(len(result.stdout) <= 16 * 1024 * 1024, 'Compiler source inventory is too large')
    rows = [unique_json(line) for line in result.stdout.splitlines() if line.strip()]
    require(len(rows) == 3 * len(names), 'Compiler source inventory is incomplete')
    return {name: {'source': rows[3*i], 'imports': rows[3*i+1], 'header': rows[3*i+2]}
            for i, name in enumerate(names)}


def collect(root, module_paths, external_modules, builtin_modules, *, query=query_headers):
    """Collect project inputs, refusing unexpected source resolution or imports.

    `module_paths` is the complete source contract inventory, not a candidate's
    self-selected subset. `external_modules` and `builtin_modules` must come
    from the independently checked package/toolchain inventory. External rows
    include their resolved source path/hash and pinned package revision. Builtin
    rows bind their compiled file hash within the pinned toolchain.
    """
    root = Path(root).absolute()
    no_links(root)
    require(isinstance(module_paths, dict) and bool(module_paths), 'Missing project module inventory')
    require(isinstance(external_modules, dict) and isinstance(builtin_modules, dict),
            'Missing external module resolution inventory')
    require(not (set(module_paths) & (set(external_modules) | set(builtin_modules)))
            and not (set(external_modules) & set(builtin_modules)),
            'A module has multiple project/package/toolchain owners')
    for name, row in external_modules.items():
        require(isinstance(name, str) and isinstance(row, dict)
                and regular_path(row.get('source_path')) and digest(row.get('source_sha256'))
                and isinstance(row.get('package'), str) and bool(row['package'])
                and isinstance(row.get('revision'), str) and bool(row['revision']),
                'Incomplete resolved package module')
    for name, row in builtin_modules.items():
        require(isinstance(name, str) and isinstance(row, dict)
                and regular_path(row.get('compiled_path')) and digest(row.get('compiled_sha256')),
                'Incomplete resolved toolchain module')
    before = {}
    for name, relative in module_paths.items():
        require(isinstance(name, str) and regular_path(name.replace('.', '/')),
                'Invalid module name')
        before[name] = read_source(root, relative)
    names = sorted(module_paths)
    records = {}
    for offset in range(0, len(names), 64):
        batch = names[offset:offset+64]
        rows = query(root, batch)
        require(isinstance(rows, dict) and set(rows) == set(batch),
                'Compiler did not return the exact requested inventory')
        for name in batch:
            row = rows[name]
            require(isinstance(row, dict) and isinstance(row.get('source'), str)
                    and isinstance(row.get('imports'), list)
                    and all(isinstance(item, str) for item in row['imports'])
                    and len(row['imports']) == len(set(row['imports']))
                    and isinstance(row.get('header'), dict), 'Malformed compiler source record')
            resolved = Path(row['source'])
            if not resolved.is_absolute():
                resolved = root / resolved
            no_links(resolved)
            require(resolved.resolve() == (root / module_paths[name]).resolve(),
                    'Compiler source resolution differs from the contract')
            imports = set(row['imports'])
            header_imports = row['header'].get('imports')
            require(isinstance(header_imports, list) and all(isinstance(item, dict)
                    and isinstance(item.get('module'), str) for item in header_imports),
                    'Malformed compiler import header')
            header_names = {item['module'] for item in header_imports}
            # Lake's imports facet omits builtins supplied by the toolchain.
            require(imports <= header_names and header_names - imports <= set(builtin_modules),
                    'Compiler import facets disagree')
            require(header_names <= set(module_paths) | set(external_modules) | set(builtin_modules),
                    'Unresolved external import; do not guess its package')
            records[name] = {'inputs': {
                'source_path': module_paths[name], 'source_sha256': before[name],
                'header': row['header'], 'project_imports': sorted(imports & set(module_paths)),
                'external_imports': {n: external_modules[n] for n in sorted(header_names & set(external_modules))},
                'builtin_imports': {n: builtin_modules[n] for n in sorted(header_names & set(builtin_modules))}}}
    for name, relative in module_paths.items():
        require(read_source(root, relative) == before[name], 'Source changed during compiler inventory')
    validate_inventory(records)
    return records
