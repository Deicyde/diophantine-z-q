"""Exercise the candidate driver on the full project, without producer authority.

This hosted dry run uses an explicitly synthetic identity only at the driver's
producer-identity boundary. Every input capture, build, full audit, staging,
archive verification and restoration uses the actual implementation. Its local
bundle is never uploaded and cannot match an authenticated GitHub producer.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from unittest.mock import patch
import zipfile

import kernel_build_driver as driver
from kernel_build_inventory import FORBIDDEN_ENV
from kernel_build_manifest import WORKFLOW, require
from kernel_build_producer import snapshot_outputs
from kernel_build_restore import BUILD_ROOTS, no_links

SCOPE = 'Full-project local driver validation; not an authenticated main producer'


def save(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True)+'\n', encoding='utf-8')


def fixture_identity(workspace):
    # These fields are a test fixture, not claimed GitHub events. The extra
    # scope field makes exact equality with authenticated_producer impossible.
    return {'repository': 'local-validation/not-an-authenticated-producer',
            'head_sha': driver.git(workspace, 'rev-parse', 'HEAD').decode().strip(),
            'run_id': 1, 'run_attempt': 1, 'event': 'workflow_dispatch',
            'ref': 'refs/heads/main', 'scope': SCOPE,
            'workflow_sha256': hashlib.sha256((workspace/WORKFLOW).read_bytes()).hexdigest()}


def preserve_project_outputs(workspace, backup):
    """Move only the two literal project output roots, never dependency outputs."""
    workspace, backup = workspace.absolute(), backup.absolute()
    no_links(workspace); no_links(backup)
    require(workspace.is_dir() and backup.parent.is_dir() and not backup.exists()
            and not backup.resolve().is_relative_to(workspace.resolve()),
            'Backup must be new and outside the project')
    moves = []
    for index, relative in enumerate(BUILD_ROOTS):
        source = workspace/relative
        no_links(source)
        require(source.resolve().is_relative_to(workspace.resolve()), 'Output root escaped project')
        if source.exists():
            require(source.is_dir(), 'Project output root is not a directory')
            moves.append((source, backup/str(index)))
    require(bool(moves), 'No built project outputs to preserve')
    backup.mkdir()
    # All resolved paths have been checked before the first reversible move.
    for source, destination in moves:
        source.rename(destination)
    return [source.relative_to(workspace).as_posix() for source, _ in moves]


def no_build_commands(modules):
    yield ['lake', '--rehash', '--no-build', 'build', 'ZInQKernel', 'GreenTaoVendor']
    for start in range(0, len(modules), 100):
        yield ['lake', '--rehash', '--no-build', 'build',
               *['+'+name for name in modules[start:start+100]]]


def probe_cached_inputs(workspace, output):
    """Observe a non-compiling traversal; never treat its exit as a build result.

    Missing project outputs are expected. This traversal can expose a dependency
    metadata change before spending an hour compiling the project. The caller
    immediately recaptures the exact prepared inputs and still runs the full
    required build and audit if the comparison passes.
    """
    require(not any(os.environ.get(k) for k in FORBIDDEN_ENV), 'No credentials allowed in probe')
    command = ['lake', '--rehash', '--no-build', 'build', 'ZInQKernel', 'GreenTaoVendor']
    with (output/'cached-input-probe.log').open('xb') as log:
        process = subprocess.run(command, cwd=workspace, stdout=log,
                                 stderr=subprocess.STDOUT, timeout=120, check=False)
    return {'command': command, 'exit_code': process.returncode,
            'scope': 'Diagnostic traversal only; neither build nor audit acceptance'}


def validate(workspace, state, output, prefix):
    require(sys.platform.startswith('linux'), 'Full-project validation must run on Linux')
    require(not any(os.environ.get(k) for k in FORBIDDEN_ENV), 'No credentials allowed in validation')
    require(not os.environ.get('GITHUB_ENV') and not os.environ.get('GITHUB_OUTPUT'),
            'Validation must not write workflow environment or outputs')
    workspace, state, output = workspace.absolute(), state.absolute(), output.absolute()
    for path in (workspace, state, output):
        no_links(path)
    require(workspace.is_dir() and state.parent.is_dir() and not state.exists()
            and not state.resolve().is_relative_to(workspace.resolve()),
            'Use fresh validation state outside the checkout')
    require(output.parent.is_dir() and not output.exists()
            and output.resolve().is_relative_to(workspace.resolve()),
            'Use a fresh evidence directory inside the checkout')
    for relative in BUILD_ROOTS:
        no_links(workspace/relative)
        require(not (workspace/relative).exists(), 'Cold validation requires absent project build outputs')
    output.mkdir(); state.mkdir()
    report = {'schema': 'kernel-reuse-project-validation/v1', 'scope': SCOPE,
              'acceptance': False, 'authenticated_reuse': False, 'status': 'running',
              'started_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'actual_execution': {k: os.environ.get(k) for k in
                ('GITHUB_REPOSITORY', 'GITHUB_SHA', 'GITHUB_REF', 'GITHUB_EVENT_NAME',
                 'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_WORKFLOW_REF')},
              'checkout_sha': driver.git(workspace, 'rev-parse', 'HEAD').decode().strip(),
              'phases': []}
    def record():
        save(output/'result.json', report)
    def phase(label, action):
        item = {'name': label, 'status': 'running'}
        report['phases'].append(item); record()
        start = time.monotonic()
        print('[project-reuse] '+label+' starting', flush=True)
        try:
            result = action()
        except Exception as error:
            item.update(status='failed', error_type=type(error).__name__)
            raise
        else:
            item.update(status='passed', result=result)
            return result
        finally:
            item['seconds'] = time.monotonic()-start
            record()
            print('[project-reuse] '+label+' '+item['status'], flush=True)
    def run(command, *, workers='2'):
        environment = dict(os.environ, LEAN_NUM_THREADS=workers)
        process = subprocess.run(command, cwd=workspace, env=environment, check=False)
        require(process.returncode == 0, 'Validation command failed: '+str(command))
        return {'command': command, 'exit_code': process.returncode, 'workers': workers}
    record()
    producer_state, consumer_state = state/'producer', state/'consumer'
    producer_state.mkdir()
    driver.write_new(producer_state/'selection.json', {'status': 'cold', 'scope': SCOPE})
    producer = fixture_identity(workspace)
    report['local_fixture_identity'] = producer
    try:
        with patch.object(driver, 'producer_identity', return_value=producer):
            phase('prepare', lambda: driver.prepare(workspace, producer_state, prefix))
            require(driver.read(producer_state/'prepared.json')['has_context'],
                    'Full-project input capture did not succeed; this dry run cannot skip producer validation')
            prepared = driver.read(producer_state/'session-prepared.json')
            modules = sorted(prepared['context']['modules'])
            report['module_count'] = len(modules)
            require(modules == sorted(driver.validate(workspace)['modules']), 'Incomplete project inventory')
            phase('cached-input-probe', lambda: probe_cached_inputs(workspace, output))
            def check_probe_inputs():
                observed, _ = driver.capture(workspace, prefix, producer_state,
                    expected=prepared['context']['environment'])
                require(observed == prepared['context'], 'Inputs changed during the non-compiling probe')
                return {'matches_prepared_context': True, 'acceptance': False}
            phase('probe-input-comparison', check_probe_inputs)
            phase('build', lambda: run(['python', '-B', 'scripts/check_kernel.py', '--phase', 'build']))
            phase('built', lambda: driver.completed_phase(workspace, producer_state, 'built'))
            phase('full-audit', lambda: run(
                ['python', '-B', 'scripts/check_kernel.py', '--phase', 'audit'], workers='1'))
            phase('finish-local-only', lambda: driver.completed_phase(workspace, producer_state, 'finish'))
        finished = driver.read(producer_state/'finished.json')
        require(finished.get('publish') is True, 'Local producer staging was not exercised')
        # Preserve the original driver result, but never expose it as a workflow
        # output or upload the bundle. This is test-only staging.
        bundle = producer_state/'bundle'
        manifest = driver.read(bundle/'manifest.json')
        consumer_state.mkdir()
        archive = consumer_state/'local-only.zip'
        def pack():
            with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=1) as zipped:
                zipped.write(bundle/'manifest.json', 'manifest.json')
                for relative in sorted(manifest['outputs']):
                    zipped.write(bundle/'outputs'/relative, 'outputs/'+relative)
            with archive.open('rb') as stream:
                digest = hashlib.file_digest(stream, 'sha256').hexdigest()
            return {'bytes': archive.stat().st_size, 'sha256': digest, 'uploaded': False}
        packed = phase('local-archive', pack)
        driver.write_new(consumer_state/'selection.json', {'status': 'selected', 'scope': SCOPE,
            'producer': producer, 'archive_sha256': packed['sha256']})
        driver.write_new(consumer_state/'download.json', {'path': str(archive), 'scope': SCOPE})
        phase('preserve-project-outputs', lambda: preserve_project_outputs(workspace, state/'cold-outputs'))
        with patch.object(driver, 'producer_identity', return_value=None):
            restored = phase('restore', lambda: driver.prepare(workspace, consumer_state, prefix))
        require(restored.get('status') == 'restored' and restored.get('modules') == modules,
                'Full project was not restored from the verified local archive')
        context = driver.read(consumer_state/'session-prepared.json')['context']
        expected = driver.read(producer_state/'session-built.json')['outputs_before_audit']
        def unchanged():
            observed = snapshot_outputs(workspace, context['modules'], context['project_paths'])
            require(observed == expected, 'Restored project outputs differ from audited output bytes')
            return {'modules': len(observed['modules']), 'output_files': len(observed['outputs']),
                    'matches_cold_audited_outputs': True}
        phase('restore-byte-equality', unchanged)
        for index, command in enumerate(no_build_commands(modules)):
            phase('no-build-'+str(index), lambda command=command: run(command))
        phase('post-no-build-byte-equality', unchanged)
        report.update(status='passed', restored_full_audit_rerun=False,
            remaining='Authenticated main producer selection and a restored full-project audit after deployment')
    except Exception as error:
        report.update(status='failed', error_type=type(error).__name__, error=str(error)[:1000])
        raise
    finally:
        report['finished_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        record()
        # Fixed evidence files only. Large local bundles and backup trees stay
        # private to this runner and are not eligible producer artifacts.
        for label, directory in (('producer', producer_state), ('consumer', consumer_state)):
            for name in ('selection.json', 'prepared.json', 'session-prepared.json',
                         'session-built.json', 'finished.json', 'input-mismatch.json'):
                source = directory/name
                if source.is_file():
                    (output/(label+'-'+name)).write_bytes(source.read_bytes())
        manifest_path = producer_state/'bundle/manifest.json'
        if manifest_path.is_file():
            (output/'local-manifest.json').write_bytes(manifest_path.read_bytes())
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--state', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--prefix', required=True, type=Path)
    args = parser.parse_args()
    validate(Path.cwd(), args.state, args.output, args.prefix)


if __name__ == '__main__':
    main()
