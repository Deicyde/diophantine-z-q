"""Snapshot and stage exact-main build outputs across the full kernel audit.

The trusted workflow calls snapshot_outputs before and after its unchanged
full audit, alongside fresh input/environment inventories. It must not run a
concurrent build while doing so. This module creates no success certificate:
consumers still require the authenticated, completed GitHub run/job/attempt.
"""
import copy
import hashlib
import json
import os
from pathlib import Path
import re

from kernel_build_environment import file_fingerprint
from kernel_build_manifest import (MAX_MANIFEST, MAX_MEMBERS, MAX_OUTPUT_BYTES, SCHEMA, digest,
    module_output_path, positive_int, require, validate_inventory, validate_manifest)
from kernel_build_restore import no_links


def canonical_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                    ensure_ascii=True).encode()).hexdigest()


def snapshot_outputs(workspace, modules, project_paths):
    workspace = Path(workspace).absolute()
    no_links(workspace)
    validate_inventory(modules)
    require(isinstance(project_paths, dict) and set(project_paths) == set(modules),
            'Output bindings do not cover the exact project inventory')
    enriched, outputs, directories, folded = copy.deepcopy(modules), {}, {}, set()
    total = 0
    for name, entry in enriched.items():
        paths = project_paths[name]
        require(paths.get('source_path') == entry['inputs']['source_path'],
                'Output binding differs from module source')
        owned = []
        for key in ('lean_output_prefix', 'ir_output_prefix'):
            prefix = paths.get(key)
            require(isinstance(prefix, str) and module_output_path(name, paths['source_path'],
                    prefix + ('.olean' if key == 'lean_output_prefix' else '.c')),
                    'Unsupported module output layout')
            base = workspace/prefix
            parent = base.parent
            no_links(parent)
            require(parent.is_dir(), 'Missing module output directory')
            if parent not in directories:
                directories[parent] = list(parent.iterdir())
            for path in directories[parent]:
                if not path.name.startswith(base.name + '.'):
                    continue
                relative = path.relative_to(workspace).as_posix()
                require(module_output_path(name, paths['source_path'], relative),
                        'Unknown module output extension; do not publish a reuse bundle')
                no_links(path)
                require(relative.casefold() not in folded, 'Multiply owned or aliased module output')
                folded.add(relative.casefold())
                require(len(folded) <= MAX_MEMBERS, 'Output file limit exceeded')
                observed = file_fingerprint(workspace.resolve(), path, maximum_bytes=MAX_OUTPUT_BYTES-total)
                outputs[relative] = {'sha256': observed['sha256'], 'size': observed['size']}
                total += observed['size']
                owned.append(relative)
        required = {paths['lean_output_prefix']+'.'+suffix for suffix in ('olean', 'ilean', 'trace')}
        required |= {paths['ir_output_prefix']+'.'+suffix for suffix in ('c', 'setup.json')}
        if entry['inputs']['header']['isModule']:
            required |= {paths['lean_output_prefix']+'.'+suffix
                         for suffix in ('olean.server', 'olean.private', 'ir', 'ir.sig')}
        require(required <= set(owned), 'Missing required Lean/Lake module output')
        entry['outputs'] = sorted(owned)
    return {'schema': 'kernel-output-snapshot/v1', 'modules': enriched, 'outputs': outputs}


def make_manifest(before, after, environment_before, environment_after,
                  build_marker, audit_report, producer):
    """Assemble only after identical inputs/outputs straddle a complete audit."""
    require(isinstance(before, dict) and before.get('schema') == 'kernel-output-snapshot/v1'
            and before == after, 'Compiled outputs or sources changed across the audit')
    require(isinstance(environment_before, dict) and bool(environment_before)
            and environment_before == environment_after, 'Build inputs/environment changed across the audit')
    require(isinstance(producer, dict) and producer.get('ref') == 'refs/heads/main'
            and producer.get('event') in {'push', 'workflow_dispatch'}
            and isinstance(producer.get('head_sha'), str)
            and re.fullmatch('[0-9a-f]{40}', producer['head_sha'])
            and isinstance(producer.get('repository'), str)
            and re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', producer['repository'])
            and positive_int(producer.get('run_id')) and positive_int(producer.get('run_attempt'))
            and digest(producer.get('workflow_sha256')), 'Missing exact-main producer context')
    require(isinstance(build_marker, dict) and build_marker.get('schema') == 'kernel-build-complete/v1'
            and build_marker.get('status') == 'complete' and isinstance(build_marker.get('identity'), dict),
            'Missing completed build marker')
    identity = build_marker['identity']
    names = sorted(before['modules'])
    require(identity.get('head_sha') == producer['head_sha'] and identity.get('modules') == names
            and digest(identity.get('contract_sha256'))
            and isinstance(identity.get('compiler'), str) and bool(identity['compiler']),
            'Completed build identity differs from the producer inventory')
    require(isinstance(audit_report, dict) and audit_report.get('schema') == 'kernel-audit/v1'
            and audit_report.get('status') == 'passed' and audit_report.get('modules') == names
            and all(audit_report.get(k) == identity[k] for k in ('head_sha', 'contract_sha256', 'compiler')),
            'Missing successful full audit of this exact build')
    manifest = {'schema': SCHEMA, 'producer': dict(producer), 'environment': environment_before,
                'modules': before['modules'], 'outputs': before['outputs'],
                'audit_report_sha256': canonical_hash(audit_report),
                'build_marker_sha256': canonical_hash(build_marker)}
    return validate_manifest(manifest, producer)


def stage_outputs(workspace, destination, manifest):
    """Copy verified bytes into a new directory, writing manifest.json last.

    Upload that directory's contents as the run's one named artifact. A partial
    stage is retained for diagnosis on failure and cannot be mistaken for a
    complete bundle because it has no manifest. Never overwrite a destination.
    """
    workspace, destination = Path(workspace).absolute(), Path(destination).absolute()
    no_links(workspace); no_links(destination)
    validate_manifest(manifest, manifest['producer'])
    encoded = (json.dumps(manifest, sort_keys=True, indent=2)+'\n').encode('utf-8')
    require(len(encoded) <= MAX_MANIFEST, 'Manifest exceeds the consumer size limit')
    require(not destination.exists() and destination.parent.is_dir(), 'Staging destination is not new')
    destination.mkdir()
    for relative, expected in manifest['outputs'].items():
        source = workspace/relative
        no_links(source)
        require(source.resolve().is_relative_to(workspace.resolve()) and source.is_file(),
                'Output source escaped the workspace')
        target = destination/'outputs'/relative
        target.parent.mkdir(parents=True, exist_ok=True)
        observed, size = hashlib.sha256(), 0
        with source.open('rb') as src, target.open('xb') as dst:
            while chunk := src.read(1024*1024):
                size += len(chunk)
                require(size <= expected['size'], 'Output grew during staging')
                observed.update(chunk); dst.write(chunk)
        require(size == expected['size'] and observed.hexdigest() == expected['sha256'],
                'Output changed after audit or during staging')
        os.chmod(target, 0o644)
    (destination/'manifest.json').write_bytes(encoded)
    return {'directory': str(destination), 'files': len(manifest['outputs']),
            'bytes': sum(row['size'] for row in manifest['outputs'].values())}
