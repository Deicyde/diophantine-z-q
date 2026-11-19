"""Run real Linux cold/reused/edited-closure full-audit comparisons.

This creates an owned four-module fixture, not a project kernel acceptance or
an authenticated GitHub producer. No external repository or dependency is
fetched. The unchanged project auditor checks every fixture declaration.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time
import traceback
import zipfile

from kernel_build_context import capture_context
from kernel_build_controls import prepare_controls, verify_controls
from kernel_build_inventory import FORBIDDEN_ENV
from kernel_build_manifest import SCHEMA, require
from kernel_build_prepare import prepare_candidate
from kernel_build_producer import snapshot_outputs, stage_outputs
from kernel_diagnostics import AuditDiagnostics


SOURCES = {
    'Fixture/Input.lean': 'def fixtureValue : Nat := 7\ntheorem fixtureValue_eq : fixtureValue = 7 := rfl\n',
    'Fixture/Independent.lean': 'theorem fixtureIndependent : True := True.intro\n',
    'Fixture/Consumer.lean': 'import Fixture.Input\ntheorem fixtureConsumer : fixtureValue + 1 = 8 := rfl\n',
    'Fixture.lean': 'import Fixture.Consumer\nimport Fixture.Independent\ntheorem fixtureExpected : fixtureValue + 1 = 8 := rfl\n',
}
PATHS = {path[:-5].replace('/', '.'): path for path in SOURCES}
CASES = ('cold', 'unchanged', 'edited-closure')
SPEC = {'modules': sorted(PATHS), 'headline': {'declaration': 'fixtureConsumer',
        'type_declaration': 'fixtureExpected'},
        'exports': ['fixtureConsumer', 'fixtureValue_eq', 'fixtureIndependent', 'fixtureExpected'], 'targets': []}


def validate(output, prefix):
    require(sys.platform.startswith('linux'), 'This validation must run on Linux')
    require(not any(os.environ.get(k) for k in FORBIDDEN_ENV), 'No credentials allowed in fixture execution')
    output, prefix = output.absolute(), prefix.resolve(strict=True)
    require(not output.exists() and output.parent.is_dir(), 'Use a fresh owned output directory')
    output.mkdir()
    workspace = output/'project'
    workspace.mkdir()
    for name, source in SOURCES.items():
        path = workspace/name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding='utf-8')
    (workspace/'lakefile.toml').write_text('name = "fixture"\nversion = "0.0.0"\ndefaultTargets = ["Fixture"]\n\n[[lean_lib]]\nname = "Fixture"\n')
    (workspace/'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
    (workspace/'lake-manifest.json').write_text(json.dumps({'version': '1.1.0',
        'packagesDir': '.lake/packages', 'packages': [], 'name': 'fixture', 'lakeDir': '.lake'}))
    (workspace/'spec.json').write_text(json.dumps(SPEC))
    (workspace/'drivers').mkdir()
    auditor = workspace/'drivers/audit_kernel.lean'
    shutil.copyfile(Path(__file__).with_name('audit_kernel.lean'), auditor)
    lake, lean = prefix/'bin/lake', prefix/'bin/lean'
    command = [str(lake), '--rehash', 'build', 'Fixture']
    drivers = ['drivers/audit_kernel.lean']
    native = [str(Path(sys.executable).resolve()), '/usr/bin/git', '/bin/bash']
    original_environment = dict(os.environ, LEAN_NUM_THREADS='1')
    report = {'schema': 'kernel-reuse-linux-validation/v1', 'status': 'running',
        'scope': 'Owned local fixture; not GitHub producer authentication or full-project acceptance',
        'started_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'auditor_sha256': hashlib.sha256(auditor.read_bytes()).hexdigest(), 'cases': []}
    def save():
        (output/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    save()

    def run(environment, controls, case, label, args, expected=0):
        verify_controls(workspace, controls, environment)
        record = {'label': label, 'command': list(map(str, args))}
        case['commands'].append(record)
        save()
        start = time.monotonic()
        with (output/(case['name']+'-'+label+'.log')).open('wb') as log:
            process = subprocess.Popen(list(map(str, args)), cwd=workspace, env=environment,
                stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                record['pid'] = process.pid
                save()
                with AuditDiagnostics(process.pid, output, name=case['name']+'-'+label):
                    code = process.wait(timeout=300)
            except BaseException:
                if process.poll() is None:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass  # The owned process exited between poll and kill.
                process.wait()
                raise
        record.update(exit_code=code, seconds=time.monotonic()-start)
        save()
        verify_controls(workspace, controls, environment)
        require(code == expected, f'{label} returned {code}, expected {expected}; see its saved log')

    def context(environment, controls, expected=None):
        return capture_context(workspace, prefix, PATHS, [command], driver_paths=drivers,
            system_drivers=native, controls=controls, environ=environment,
            expected_environment=expected,
            progress=lambda phase: print('[fixture] '+phase, flush=True))

    # No GitHub run is invented for a fixture. Its explicit local identity can
    # exercise the byte verifier but is never passed to the GitHub authenticator.
    producer = {'scope': 'owned Linux validation fixture, not a GitHub producer'}
    archive_path = output/'local-fixture-only.zip'
    baseline = expected_environment = selection = None
    try:
        for name in CASES:
            case = {'name': name, 'commands': []}
            report['cases'].append(case)
            controls = output/(name+'-controls')
            environment, _ = prepare_controls(workspace, controls, environ=original_environment)
            if name == 'edited-closure':
                (workspace/'Fixture/Input.lean').write_text(SOURCES['Fixture/Input.lean'].replace(':= 7\n', ':= 3 + 4\n', 1))
            start = time.monotonic()
            if name == 'cold':
                before, detail = context(environment, controls)
            else:
                with archive_path.open('rb') as archive:
                    restored, before, detail = prepare_candidate(workspace, prefix, PATHS, [command],
                        selection=selection, archive=archive, driver_paths=drivers,
                        system_drivers=native, controls=controls, environ=environment)
                case['restore'] = restored
                require(restored['status'] == 'restored', 'Fixture restoration rejected: '+json.dumps(restored))
                require(restored['modules'] == (sorted(PATHS) if name == 'unchanged' else ['Fixture.Independent']),
                        'Restored modules differ from the expected unchanged closure')
                if name == 'unchanged':
                    run(environment, controls, case, 'no-build', [lake, '--rehash', '--no-build', 'build', 'Fixture'])
                else:
                    run(environment, controls, case, 'independent-no-build', [lake, '--rehash', '--no-build', 'build', '+Fixture.Independent'])
                    run(environment, controls, case, 'changed-needs-build', [lake, '--rehash', '--no-build', 'build', '+Fixture.Input'], 3)
            case['preparation_seconds'] = time.monotonic()-start
            (output/(name+'-inputs-before.json')).write_text(json.dumps(detail, indent=2))
            run(environment, controls, case, 'build', command)
            built, _ = context(environment, controls, expected=before['environment'])
            require(built == before, 'Fixture inputs changed during compilation')
            compiled = snapshot_outputs(workspace, built['modules'], built['project_paths'])
            run(environment, controls, case, 'audit', [lake, 'env', lean, '-j', '1', '--run',
                auditor, workspace/'spec.json', workspace/'audit.json'])
            after, _ = context(environment, controls, expected=before['environment'])
            require(after == before, 'Fixture inputs changed during the full audit')
            require(snapshot_outputs(workspace, after['modules'], after['project_paths']) == compiled,
                    'Fixture outputs changed during the full audit')
            audit = json.loads((workspace/'audit.json').read_text())
            require(audit['status'] == 'passed' and audit['modules'] == sorted(PATHS), 'Incomplete fixture audit')
            if baseline is None:
                baseline = audit
                expected_environment = before['environment']
                manifest = {'schema': SCHEMA, 'producer': producer, 'environment': expected_environment,
                            'modules': compiled['modules'], 'outputs': compiled['outputs']}
                stage_outputs(workspace, output/'fixture-bundle', manifest)
                with zipfile.ZipFile(archive_path, 'x', zipfile.ZIP_DEFLATED) as archive:
                    for path in (output/'fixture-bundle').rglob('*'):
                        if path.is_file():
                            archive.write(path, path.relative_to(output/'fixture-bundle').as_posix())
                selection = {'status': 'selected', 'producer': producer,
                             'archive_sha256': hashlib.sha256(archive_path.read_bytes()).hexdigest()}
            require(audit == baseline, 'Complete audit report differs from the cold fixture')
            case.update(audit=audit, audit_equal_to_cold=True, inputs_and_outputs_unchanged=True)
            save()
            # Preserve this fixture's build tree; never clean a dependency or an
            # existing project. All variants keep the same runtime search paths.
            source, destination = workspace/'.lake/build', output/(name+'-build')
            require(source.resolve().is_relative_to(workspace.resolve())
                    and destination.parent == output and not destination.exists(), 'Unsafe fixture output move')
            source.rename(destination)
        require(hashlib.sha256(auditor.read_bytes()).hexdigest() == report['auditor_sha256'], 'Auditor changed')
        report['status'] = 'passed'
    except Exception:
        report.update(status='failed', error=traceback.format_exc())
        raise
    finally:
        report['completed_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        save()
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--prefix', required=True, type=Path)
    args = parser.parse_args()
    print(json.dumps({'status': validate(args.output, args.prefix)['status'], 'output': str(args.output)}))
