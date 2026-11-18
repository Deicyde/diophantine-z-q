"""Trusted workflow entry points for verified main-output reuse.

Install this driver and its imports from the protected default branch before
candidate execution. Only `select` receives a step-scoped GitHub read token.
Other phases run without API/artifact credentials. The workflow still runs
check_kernel.py's complete build and audit between these phases.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.error

from check_kernel_contract import git, validate
from kernel_build_context import capture_context
from kernel_build_changes import InputContextMismatch
from kernel_build_controls import prepare_controls, verify_controls, SETTINGS
from kernel_build_download import download_archive
from kernel_build_inventory import FORBIDDEN_ENV
from kernel_build_manifest import WORKFLOW, positive_int, require, unique_json
from kernel_build_prepare import prepare_candidate
from kernel_build_restore import no_links
from kernel_build_session import begin, record_build, finish
from kernel_build_source import GitHub, select_producer


SCHEMA = 'kernel-build-driver/v1'
BUILD_COMMANDS = [['python', '-B', 'scripts/check_kernel.py', '--phase', 'build']]


def write_new(path, value):
    no_links(path)
    raw = (json.dumps(value, sort_keys=True, indent=2)+'\n').encode('utf-8')
    with path.open('xb') as stream:
        stream.write(raw)


def read(path):
    no_links(path)
    require(path.is_file() and path.stat().st_size <= 128*1024*1024, 'Missing or oversized driver state')
    return unique_json(path.read_bytes())


def checked_state(workspace, state):
    workspace, state = Path(workspace).absolute(), Path(state).absolute()
    no_links(workspace); no_links(state)
    require(workspace.is_dir() and state.is_dir()
            and not state.resolve().is_relative_to(workspace.resolve()),
            'Trusted driver state must be outside the candidate checkout')
    require(not any(os.environ.get(k) for k in FORBIDDEN_ENV),
            'Build driver must run without API or artifact credentials')
    return workspace, state


def producer_identity(workspace, environment):
    """Only exact-main push/dispatch executions may publish a producer bundle."""
    if environment.get('GITHUB_REF') != 'refs/heads/main' or environment.get('GITHUB_EVENT_NAME') not in (
            'push', 'workflow_dispatch'):
        return None
    repository, sha = environment.get('GITHUB_REPOSITORY'), environment.get('GITHUB_SHA')
    require(isinstance(repository, str) and re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository)
            and isinstance(sha, str) and re.fullmatch('[0-9a-f]{40}', sha),
            'Missing main-run repository or commit')
    require(git(workspace, 'rev-parse', 'HEAD').decode().strip() == sha,
            'Producer checkout is not the main run commit')
    run_id, attempt = int(environment.get('GITHUB_RUN_ID', '0')), int(environment.get('GITHUB_RUN_ATTEMPT', '0'))
    require(positive_int(run_id) and positive_int(attempt), 'Missing producer run/attempt')
    return {'repository': repository, 'head_sha': sha, 'run_id': run_id, 'run_attempt': attempt,
            'event': environment['GITHUB_EVENT_NAME'], 'ref': 'refs/heads/main',
            'workflow_sha256': hashlib.sha256((workspace/WORKFLOW).read_bytes()).hexdigest()}


def capture(workspace, prefix, state, *, expected=None, prepare_cache_metadata=False):
    contract = validate(workspace)
    inputs = ['scripts/'+p.name for p in Path(__file__).parent.glob('kernel_build_*.py')]
    inputs += ['scripts/check_kernel.py', 'scripts/check_kernel_contract.py', 'scripts/check_target.py',
               'scripts/audit_kernel.lean', 'scripts/kernel_diagnostics.py']
    try:
        return capture_context(workspace, prefix, contract['modules'], BUILD_COMMANDS,
            driver_paths=sorted(inputs), system_drivers=[str(Path(sys.executable).resolve()), '/usr/bin/git', '/bin/bash'],
            controls=state/'controls', expected_environment=expected,
            prepare_cache_metadata=prepare_cache_metadata,
            progress=lambda message: print('[kernel-reuse] '+message, flush=True))
    except InputContextMismatch as error:
        previous = read(state/'inputs-before.json') if (state/'inputs-before.json').exists() else None
        # Preserve bounded mismatch evidence before the unchanged fatal refusal.
        # This record is diagnostic and never becomes a new accepted baseline.
        write_new(state/'input-mismatch.json', error.report(previous))
        raise


def select(state, repository, approved_workflow):
    state = Path(state).absolute()
    no_links(state)
    require(not state.exists() and state.parent.is_dir(), 'Selector needs a fresh state directory')
    state.mkdir()
    token = os.environ.get('GH_TOKEN')
    try:
        selection = select_producer(GitHub(token), repository, approved_workflow)
        if selection['status'] == 'selected':
            download = download_archive(selection, token, state)
            write_new(state/'download.json', download)
    except (ValueError, OSError, urllib.error.URLError) as error:
        # Error type only: an exception can contain a request URL or headers.
        selection = {'status': 'cold', 'reason': 'Producer selection/download unavailable',
                     'error_type': type(error).__name__}
    write_new(state/'selection.json', selection)
    return {'phase': 'selected', 'status': selection['status']}


def prepare(workspace, state, prefix):
    workspace, state = checked_state(workspace, state)
    require(not (state/'prepared.json').exists(), 'Prepared state already exists; do not replay')
    environment, _ = prepare_controls(workspace, state/'controls')
    # Apply only explicit cache controls in this process; native queries inspect
    # the actual process environment as well as the supplied child environment.
    os.environ.update(environment)
    for key in ('LAKE_CACHE_ARTIFACT_ENDPOINT', 'LAKE_CACHE_REVISION_ENDPOINT', 'LAKE_CACHE_SERVICE'):
        os.environ.pop(key, None)
    if os.environ.get('GITHUB_ENV'):
        with Path(os.environ['GITHUB_ENV']).open('a', encoding='utf-8') as target:
            for key in (*SETTINGS, 'LAKE_CONFIG', 'LAKE_CACHE_DIR'):
                value = environment[key]
                require('\n' not in value and '\r' not in value, 'Unsafe workflow environment value')
                target.write(key+'='+value+'\n')
            # An empty endpoint is equivalent to absent only after explicitly
            # removing it in this driver's subsequent processes below.
            for key in ('LAKE_CACHE_ARTIFACT_ENDPOINT', 'LAKE_CACHE_REVISION_ENDPOINT', 'LAKE_CACHE_SERVICE'):
                target.write(key+'=\n')
    selection = read(state/'selection.json')
    producer = producer_identity(workspace, environment)
    context = detail = None
    if selection.get('status') == 'selected':
        download = read(state/'download.json')
        archive_path = Path(download['path'])
        no_links(archive_path)
        require(archive_path.resolve().parent == state.resolve(), 'Archive escaped driver state')
        contract = validate(workspace)
        inputs = ['scripts/'+p.name for p in Path(__file__).parent.glob('kernel_build_*.py')]
        inputs += ['scripts/check_kernel.py', 'scripts/check_kernel_contract.py', 'scripts/check_target.py',
                   'scripts/audit_kernel.lean', 'scripts/kernel_diagnostics.py']
        with archive_path.open('rb') as stream:
            result, context, detail = prepare_candidate(workspace, prefix, contract['modules'], BUILD_COMMANDS,
                selection=selection, archive=stream, driver_paths=sorted(inputs),
                system_drivers=[str(Path(sys.executable).resolve()), '/usr/bin/git', '/bin/bash'],
                controls=state/'controls', environ=environment)
    else:
        result = {'status': 'cold', 'reason': 'No authenticated producer selected', 'audit_required': True}
    if context is None and producer is not None:
        try:
            context, detail = capture(workspace, prefix, state, prepare_cache_metadata=True)
        except (ValueError, OSError, subprocess.TimeoutExpired) as error:
            result['producer_unavailable'] = type(error).__name__
    if context is not None:
        write_new(state/'session-prepared.json', begin(context))
        write_new(state/'inputs-before.json', detail)
        if detail.get('metadata_preparation') is not None:
            write_new(state/'metadata-preparation.json', detail['metadata_preparation'])
    config = {'schema': SCHEMA, 'workspace': str(workspace.resolve()), 'prefix': str(Path(prefix).resolve()),
              'producer': producer, 'has_context': context is not None, 'result': result}
    write_new(state/'prepared.json', config)
    return result


def completed_phase(workspace, state, phase):
    workspace, state = checked_state(workspace, state)
    config = read(state/'prepared.json')
    require(config.get('schema') == SCHEMA and config.get('workspace') == str(workspace.resolve()),
            'Driver state belongs to a different checkout')
    for key in ('LAKE_CACHE_ARTIFACT_ENDPOINT', 'LAKE_CACHE_REVISION_ENDPOINT', 'LAKE_CACHE_SERVICE'):
        require(not os.environ.get(key), 'Unexpected cache endpoint after preparation')
        os.environ.pop(key, None)
    verify_controls(workspace, state/'controls', dict(os.environ))
    if not config['has_context']:
        return {'phase': phase, 'publish': False, 'reason': 'No eligible producer context'}
    prepared = read(state/'session-prepared.json')
    context, detail = capture(workspace, config['prefix'], state, expected=prepared['context']['environment'])
    marker = read(workspace/'build/kernel-ci/build-complete.json')
    if phase == 'built':
        built = record_build(workspace, prepared, context, marker)
        write_new(state/'session-built.json', built)
        write_new(state/'inputs-built.json', detail)
        return {'phase': 'built', 'publish': False}
    require(phase == 'finish', 'Unknown completion phase')
    built = read(state/'session-built.json')
    audit = read(workspace/'build/kernel-ci/audit.json')
    # A PR can consume outputs, never publish reusable main evidence.
    if config['producer'] is None:
        from kernel_build_producer import snapshot_outputs
        require(context == built['context'] and marker == built['build_marker']
                and snapshot_outputs(workspace, context['modules'], context['project_paths']) == built['outputs_before_audit'],
                'Consumer inputs or outputs changed during the full audit')
        identity = marker['identity']
        require(audit.get('schema') == 'kernel-audit/v1' and audit.get('status') == 'passed'
                and all(audit.get(key) == identity[key] for key in ('head_sha', 'contract_sha256', 'compiler', 'modules')),
                'Missing successful full audit of the consumer build')
        result = {'phase': 'finish', 'publish': False, 'reason': 'Not an exact-main producer'}
    else:
        require(producer_identity(workspace, dict(os.environ)) == config['producer'], 'Producer identity changed')
        result = finish(workspace, state/'bundle', built, context, marker, audit, config['producer'])
        result['publish'] = True
    write_new(state/'inputs-finished.json', detail)
    write_new(state/'finished.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=['select', 'prepare', 'built', 'finish'])
    parser.add_argument('--state', required=True, type=Path)
    parser.add_argument('--workspace', type=Path)
    parser.add_argument('--prefix', type=Path)
    parser.add_argument('--repository')
    parser.add_argument('--approved-workflow')
    args = parser.parse_args()
    if args.phase == 'select':
        result = select(args.state, args.repository, args.approved_workflow)
    elif args.phase == 'prepare':
        require(args.workspace is not None and args.prefix is not None, 'Workspace and toolchain prefix required')
        result = prepare(args.workspace, args.state, args.prefix)
    else:
        require(args.workspace is not None, 'Workspace required')
        result = completed_phase(args.workspace, args.state, args.phase)
    print(json.dumps(result, sort_keys=True))
    if args.phase == 'finish' and os.environ.get('GITHUB_OUTPUT'):
        with Path(os.environ['GITHUB_OUTPUT']).open('a', encoding='utf-8') as stream:
            stream.write('publish='+str(result.get('publish', False)).lower()+'\n')


if __name__ == '__main__':
    main()
