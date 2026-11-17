"""Validate immutable main-build bundles before any output is restored.

This library does not select GitHub runs, download artifacts, or install files.
Its caller must obtain producer facts and the archive digest from authenticated
GitHub responses, not from the candidate or the bundle. Workflow integration
must keep those operations separate from candidate execution.
"""
import hashlib
import json
import re
import stat
import zipfile

SCHEMA = 'kernel-main-build/v1'
WORKFLOW = '.github/workflows/kernel-lean.yml'
JOB = 'Complete kernel build and exact-target audit'
MAX_MANIFEST = 16 * 1024 * 1024
MAX_OUTPUT_BYTES = 16 * 1024 ** 3
MAX_MEMBERS = 100000


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(value):
    return isinstance(value, str) and re.fullmatch(r'[0-9a-f]{64}', value) is not None


def positive_int(value):
    return type(value) is int and value > 0


def nested(value, key):
    field = value.get(key)
    return field if isinstance(field, dict) else {}


def regular_path(value):
    return (isinstance(value, str) and bool(value) and not value.startswith('/')
            and not any(c in value for c in ('\\', ':', '\x00'))
            and all(part not in ('', '.', '..') for part in value.split('/')))


def output_path(value):
    return regular_path(value) and value.startswith(('.lake/build/', 'lean/.lake/build/'))


def unique_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate JSON key')
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('Non-finite JSON value')))


def authenticated_producer(run, job, artifact, *, repository, approved_workflow_sha256,
                           observed_workflow_sha256, main_commit, archive_sha256):
    """Bind independently fetched API facts; caller separately proves main ancestry.

    Artifact upload is not itself a completed producer. Both the exact attempt's
    job and the complete run must have succeeded before this function admits it.
    """
    require(digest(archive_sha256) and digest(approved_workflow_sha256)
            and observed_workflow_sha256 == approved_workflow_sha256,
            'Unapproved workflow or invalid artifact digest')
    require(isinstance(main_commit, str) and re.fullmatch(r'[0-9a-f]{40}', main_commit),
            'Invalid main commit')
    require(isinstance(run, dict) and isinstance(job, dict) and isinstance(artifact, dict),
            'Malformed producer API response')
    require(positive_int(run.get('id')) and positive_int(run.get('run_attempt'))
            and nested(run, 'repository').get('full_name') == repository
            and nested(run, 'head_repository').get('full_name') == repository
            and run.get('event') == 'push' and run.get('head_branch') == 'main'
            and run.get('head_sha') == main_commit and run.get('path') == WORKFLOW
            and run.get('status') == 'completed' and run.get('conclusion') == 'success',
            'Run is not a successful exact-main producer')
    require(positive_int(job.get('id')) and job.get('run_id') == run['id']
            and type(job.get('run_id')) is int
            and job.get('run_attempt') == run['run_attempt']
            and type(job.get('run_attempt')) is int
            and job.get('head_sha') == main_commit and job.get('name') == JOB
            and job.get('status') == 'completed' and job.get('conclusion') == 'success',
            'Producer job or attempt did not succeed')
    require(positive_int(artifact.get('id')) and artifact.get('expired') is False
            and nested(artifact, 'workflow_run').get('id') == run['id']
            and type(nested(artifact, 'workflow_run').get('id')) is int
            and nested(artifact, 'workflow_run').get('head_sha') == main_commit
            and artifact.get('name') == f"kernel-main-build-{run['id']}-{run['run_attempt']}"
            and artifact.get('digest') == 'sha256:' + archive_sha256,
            'Artifact does not bind this producer attempt')
    # This expected record comes from API facts. No bundle field can supply it.
    return {'repository': repository, 'head_sha': main_commit,
            'run_id': run['id'], 'run_attempt': run['run_attempt'],
            'workflow_sha256': approved_workflow_sha256}


def validate_inventory(modules):
    require(isinstance(modules, dict) and bool(modules), 'Empty module inventory')
    folded_paths = set()
    for name, entry in modules.items():
        require(isinstance(name, str) and bool(name) and regular_path(name.replace('.', '/'))
                and isinstance(entry, dict),
                'Malformed module entry')
        inputs = entry.get('inputs')
        require(isinstance(inputs, dict) and regular_path(inputs.get('source_path'))
                and inputs['source_path'].endswith('.lean')
                and digest(inputs.get('source_sha256'))
                and isinstance(inputs.get('header'), dict)
                and isinstance(inputs.get('project_imports'), list)
                and all(isinstance(dep, str) and dep in modules for dep in inputs['project_imports'])
                and len(inputs['project_imports']) == len(set(inputs['project_imports'])),
                'Incomplete module source/import inventory')
        header = inputs['header']
        require(type(header.get('isModule')) is bool and isinstance(header.get('imports'), list)
                and all(isinstance(imp, dict) and isinstance(imp.get('module'), str)
                        and bool(imp['module']) and all(type(imp.get(k)) is bool
                            for k in ('isMeta', 'isExported', 'importAll'))
                        for imp in header['imports']), 'Malformed compiler import header')
        require(set(inputs['project_imports']) == {
            imp['module'] for imp in header['imports'] if imp['module'] in modules},
            'Compiler header and project import inventory disagree')
        path = inputs['source_path'].casefold()
        require(path not in folded_paths, 'Aliased module source path')
        folded_paths.add(path)


def reusable_modules(old, current, old_environment, current_environment):
    """Exact input equality and all project predecessors unchanged, without recursion.

    Environment equality must include compiler, all package configuration and
    revisions, options, platform, and external-module resolution. Source/header
    inventories must come from the compiler/Lake, not a regex approximation.
    """
    validate_inventory(old)
    validate_inventory(current)
    require(isinstance(old_environment, dict) and bool(old_environment)
            and isinstance(current_environment, dict) and bool(current_environment),
            'Missing compiler/package environment')
    if old_environment != current_environment:
        return set()
    dependents = {name: [] for name in current}
    missing = {}
    for name, entry in current.items():
        deps = entry['inputs']['project_imports']
        missing[name] = len(deps)
        for dep in deps:
            dependents[dep].append(name)
    queue = [name for name, count in missing.items() if count == 0]
    reused, visited = set(), set()
    while queue:
        name = queue.pop()
        inputs = current[name]['inputs']
        if (name in old and old[name]['inputs'] == inputs
                and all(dep in reused for dep in inputs['project_imports'])):
            reused.add(name)
        visited.add(name)
        for dependent in dependents[name]:
            missing[dependent] -= 1
            if missing[dependent] == 0:
                queue.append(dependent)
    require(visited == set(current), 'Cyclic or incomplete module dependency graph')
    return reused


def validate_manifest(manifest, producer):
    require(isinstance(manifest, dict) and manifest.get('schema') == SCHEMA
            and manifest.get('producer') == producer, 'Wrong bundle producer or schema')
    validate_inventory(manifest.get('modules'))
    require(isinstance(manifest.get('environment'), dict) and bool(manifest['environment']),
            'Missing build environment')
    outputs = manifest.get('outputs')
    require(isinstance(outputs, dict) and bool(outputs) and len(outputs) <= MAX_MEMBERS,
            'Missing or excessive output inventory')
    owned, folded = set(), set()
    total = 0
    for path, row in outputs.items():
        require(output_path(path) and path.casefold() not in folded and isinstance(row, dict)
                and digest(row.get('sha256')) and type(row.get('size')) is int and row['size'] >= 0,
                'Malformed or aliased compiled output')
        folded.add(path.casefold())
        total += row['size']
    require(total <= MAX_OUTPUT_BYTES, 'Compiled outputs exceed the size limit')
    for name, entry in manifest['modules'].items():
        paths = entry.get('outputs')
        require(isinstance(paths, list) and bool(paths), 'Missing module outputs')
        root = 'lean/' if entry['inputs']['source_path'].startswith('lean/') else ''
        prefixes = [root + '.lake/build/' + directory + name.replace('.', '/') + '.'
                    for directory in ('lib/lean/', 'ir/')]
        for path in paths:
            require(isinstance(path, str) and path in outputs and path not in owned,
                    'Missing, duplicated or multiply owned output')
            require(any(path.startswith(prefix) for prefix in prefixes),
                    'Output path does not belong to its module')
            owned.add(path)
        require(any(p.endswith('.olean') for p in paths)
                and any(p.endswith('.trace') for p in paths), 'Incomplete Lean module outputs')
    require(owned == set(outputs), 'Unowned output in bundle')
    return manifest


def verify_archive(stream, archive_sha256, producer):
    """Verify an open, seekable downloaded artifact; never extract or install files.

    Keep this handle open through later staging. Its SHA-256 is the independently
    authenticated GitHub artifact digest, not a checksum stored in the bundle.
    Every output is streamed and hashed, including outputs not selected for reuse.
    """
    require(digest(archive_sha256), 'Invalid authenticated archive digest')
    stream.seek(0)
    observed = hashlib.file_digest(stream, 'sha256').hexdigest()
    require(observed == archive_sha256, 'Downloaded artifact digest mismatch')
    stream.seek(0)
    with zipfile.ZipFile(stream) as bundle:
        members = bundle.infolist()
        require(0 < len(members) <= MAX_MEMBERS + 1, 'Invalid archive member count')
        seen, folded = {}, set()
        for row in members:
            name = row.filename
            mode = row.external_attr >> 16
            require(regular_path(name) and name not in seen and name.casefold() not in folded
                    and not row.is_dir() and not row.flag_bits & 1
                    and stat.S_IFMT(mode) in (0, stat.S_IFREG),
                    'Unsafe, encrypted, duplicate or non-file archive member')
            require(name == 'manifest.json' or (name.startswith('outputs/')
                    and output_path(name[len('outputs/'):])), 'Unexpected archive member')
            require(0 <= row.file_size <= MAX_OUTPUT_BYTES, 'Excessive archive member size')
            seen[name] = row
            folded.add(name.casefold())
        require('manifest.json' in seen and seen['manifest.json'].file_size <= MAX_MANIFEST,
                'Missing or oversized manifest')
        manifest = validate_manifest(unique_json(bundle.read('manifest.json')), producer)
        require(set(seen) == {'manifest.json'} | {'outputs/' + p for p in manifest['outputs']},
                'Archive and manifest inventories differ')
        for path, expected in manifest['outputs'].items():
            member = seen['outputs/' + path]
            require(member.file_size == expected['size'], 'Output size mismatch')
            with bundle.open(member) as data:
                observed = hashlib.file_digest(data, 'sha256').hexdigest()
            require(observed == expected['sha256'], 'Compiled output hash mismatch')
    return manifest
