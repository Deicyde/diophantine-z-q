"""Rebuild the 389-variable proposal, coefficient variants, and portable audits.

The arithmetic characterization remains conditional on the written inherited
inputs; neither this program nor the finite checkers proves those theorems.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
AUDIT = PACKAGE/'audit'
CHAINS = ['788,788', '338,338,336', '158,158,158,152']
completed_stages = []


def atomic_json(path, value):
    temporary = path.with_name(path.name+'.tmp')
    with temporary.open('w', encoding='utf-8', newline='\n') as stream:
        stream.write(json.dumps(value, indent=2)+'\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def run(stage, *arguments):
    if stage in completed_stages:
        raise ValueError('Duplicate pipeline stage: '+stage)
    print('Running stage: '+stage, flush=True)
    result = subprocess.run([str(a) for a in arguments], cwd=HERE)
    progress = {'format': 'conditional-quartic-pipeline-progress-v1',
                'completedStages': list(completed_stages),
                'currentStage': stage, 'returnCode': result.returncode}
    if result.returncode:
        progress['status'] = 'FAIL'
        atomic_json(PACKAGE/'pipeline-progress.json', progress)
        raise subprocess.CalledProcessError(result.returncode, result.args)
    completed_stages.append(stage)
    progress.update(status='IN_PROGRESS', completedStages=list(completed_stages))
    atomic_json(PACKAGE/'pipeline-progress.json', progress)


run('build_source', 'node', HERE/'builder.cjs')
run('build_reference_source', 'node', HERE/'reference_round7/builder.cjs')
run('compile_source', sys.executable, HERE/'tools/compile_ir.py', HERE/'raw-translated-ir.json', HERE/'compiled')
run('verify_gates', 'node', HERE/'tools/checker.cjs', '--input', HERE/'raw-translated-ir.json',
    '--compiled', HERE/'compiled/compiled-ir.json',
    '--certificate', HERE/'compiled/reduction-certificate.json',
    '--coordinate-map', HERE/'compiled/coordinate-map.json',
    '--quartic', HERE/'compiled/polynomial.json', '--report', HERE/'independent-gate-check.json')
run('reduce_rows', sys.executable, HERE/'tools/run_pipeline.py', HERE/'compiled/compiled-ir.json', HERE/'final', '--orders', 2)
chain_arguments = [x for chain in CHAINS for x in ['--chain', chain]]
run('lift_constants', sys.executable, HERE/'finish_tables.py', HERE, *chain_arguments)
run('verify_detector', sys.executable, AUDIT/'check_detector_source.py', HERE, '--anchor', '3^2364', '--high', 45,
    '--report', HERE/'detector-source-check.json')
run('independent_detector', sys.executable, AUDIT/'check_detector_promotion_independent.py', HERE,
    '--baseline', HERE/'reference_round7', '--expected-exponent', 2364,
    '--proof', PACKAGE/'proofs/detector_round8.tex',
    '--report', AUDIT/'detector-independent-check.json')
run('verify_package', sys.executable, HERE/'verify_package.py', HERE, '--detector-assertions', 384)
run('verify_symbolic', 'node', HERE/'check_final.cjs')
run('specialize', sys.executable, HERE/'specialize_core.py', HERE, '--expected-exponent', 2364)
run('write_tables', sys.executable, HERE/'write_tables_text.py', HERE)
run('balance', sys.executable, HERE/'balance_coefficients.py', HERE)
run('verify_geometry', sys.executable, AUDIT/'check_geometry_round7.py', HERE,
    '--scalar-order', 28, '--report', AUDIT/'geometry-check.json')
run('independent_scalar', sys.executable, AUDIT/'check_scalar_independent.py', HERE,
    '--proof', PACKAGE/'proofs/geometry_round7.tex', '--report', AUDIT/'scalar-independent-check.json')
run('verify_arithmetic', sys.executable, AUDIT/'check_arithmetic_round8.py', HERE,
    '--expected-exponent', 2364, '--high-order', 45,
    '--proof', PACKAGE/'proofs/arithmetic_round8.tex', '--report', AUDIT/'arithmetic-check.json')
run('independent_arithmetic', sys.executable, AUDIT/'check_arithmetic_round8_independent.py',
    '--directory', HERE, '--proof', PACKAGE/'proofs/arithmetic_round8.tex',
    '--report', AUDIT/'arithmetic-independent-check.json')
run('verify_chains', sys.executable, AUDIT/'check_scaled_chains_independent.py', HERE,
    '--report', AUDIT/'scaled-chain-independent-check.json')
run('second_scalar', sys.executable, AUDIT/'check_scalar_second_review.py', HERE,
    '--report', AUDIT/'scalar-second-review-check.json')
run('verify_parameter_binding', sys.executable, AUDIT/'check_parameter_binding.py', HERE/'tools',
    '--report', AUDIT/'parameter-binding-check.json')
run('verify_stage_bridges', sys.executable, AUDIT/'check_integrated_bridges.py', HERE,
    '--expected-exponent', 2364, '--report', AUDIT/'integrated-bridge-check.json')
run('verify_diagonal', sys.executable, AUDIT/'check_diagonal_scaling.py', HERE,
    '--expected-exponent', 2364, '--expected-coordinates', 389,
    '--expected-residuals', 357, '--expected-monomials', 26295,
    '--expected-max-digits', 757, '--expected-max-bits', 2513,
    '--report', AUDIT/'diagonal-scaling-check.json')
source_reports = ['detector-independent-check.json', 'geometry-check.json', 'scalar-independent-check.json',
                  'arithmetic-check.json', 'arithmetic-independent-check.json', 'scalar-second-review-check.json',
                  'scaled-chain-independent-check.json', 'integrated-bridge-check.json']
arguments = [x for name in source_reports for x in ['--source-report', AUDIT/name]]
run('verify_delivered_tables', sys.executable, AUDIT/'check_delivered_quartics_round8.py', PACKAGE,
    '--expected-exponent', 2364, '--expected-core', 389, '--expected-residuals', 357,
    '--expected-monomials', 26295, '--expected-detector-assertions', 384, '--high-order', 45,
    *chain_arguments, '--package-audit', *arguments, '--report', AUDIT/'delivered-quartics-check.json')
atomic_json(PACKAGE/'pipeline-completion.json', {
    'format': 'conditional-quartic-pipeline-completion-v1', 'status': 'PASS',
    'pipelineSha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'completedStages': completed_stages,
})
print('PASS: fresh construction, every coefficient table, and every portable audit.', flush=True)
