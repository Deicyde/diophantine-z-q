"""Research-only kernel skips agree with the real review gate, without providers."""
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from test_gate import FakeGH, HEAD, ROOT, changed, gate

# Actual complete changed-path list for PR158 at 723e2699d079e395b937e9f82e1b179a67a2303b.
# File contents are immaterial to the two scope selectors; no contributor code runs.
PR158_PATHS = ['research/brox-explicit229-v68/' + name for name in """DEPENDENCY_INDEX.md
PR_DESCRIPTION.md
README.md
REVIEW_NOTE.md
REVIEW_RESPONSE.md
REVIEW_RESPONSE_ROUND2.md
arithmetic_certificate.json
build.py
certificate.json
check.py
check_arithmetic.py
check_graft.py
check_independent.py
check_source_bridge.py
contact-change.json
graft.json
official_measurement.json
paper.tex
polynomial.json
quadratic.json
quartic229-N15.txt
source/PROVENANCE229.json
source/original_graft_certificate.json
source/quadratic195.json
source/quadratic229-v62.json
source/transformation195.json
source_bridge_certificate.json
source_paper.tex
suppliers/effective_torsion_sums_20261117_v62.tex
transformation.json
upstream/explicit-record-README.md
upstream/measure_plain_text.py""".splitlines()]
KERNEL_CHECK = 'Complete kernel build and exact-target audit'
spec = importlib.util.spec_from_file_location('research_kernel_scope', ROOT / 'scripts/kernel_pr_scope.py')
scope = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scope)


class ResearchScopeGateTests(unittest.TestCase):
    def setUp(self):
        self.files = [changed(path) for path in PR158_PATHS]
        self.gh = FakeGH()
        self.gh.pr['changed_files'] = len(self.files)
        original = self.gh.pages
        self.gh.pages = lambda path: self.files if path.endswith('/files') else original(path)

    def tearDown(self):
        gate.configure_budget([])

    def test_pr158_skips_kernel_build_without_entering_lean_evidence_wait(self):
        self.assertEqual(len(self.files), 32)
        pinned = set(json.loads((ROOT / 'KERNEL_CONTRACT.json').read_text())['files'])
        self.assertTrue(scope.research_only_inputs(PR158_PATHS, pinned))
        self.assertFalse(gate.lean_profile_eligible(self.files))
        self.assertEqual(gate.configure_budget(self.files)['context_token_budget'], 900000)
        with tempfile.TemporaryDirectory() as tmp:
            event = Path(tmp) / 'event.json'
            event.write_text(json.dumps({'pull_request': {'number': 1}}))
            env = {'MODE': 'live', 'GITHUB_REF': 'refs/heads/main',
                   'GITHUB_REPOSITORY': 'x/y', 'GH_TOKEN': 'fixture',
                   'GITHUB_EVENT_PATH': str(event)}
            with patch.dict(os.environ, env), patch.object(gate, 'OUT', Path(tmp)), \
                    patch.object(gate, 'GitHub', return_value=self.gh), \
                    patch.object(gate, 'lean_evidence') as evidence, \
                    patch.object(gate, 'ensure_kernel_dispatch') as dispatch, \
                    patch.object(gate.time, 'sleep') as sleep, \
                    patch.object(gate, 'model_turn') as provider:
                gate.wait_lean()
                result = json.loads((Path(tmp) / 'lean-preflight.json').read_text())
                self.assertEqual(result, {'eligible': False, 'ready': False})
                evidence.assert_not_called()
                dispatch.assert_not_called()
                sleep.assert_not_called()
                provider.assert_not_called()

    def test_successful_required_job_accepts_skipped_compilation_steps(self):
        requirements = [{'context': name, 'integration_id': 15368}
                        for name in sorted(gate.REQUIRED_COMPUTATIONS)]
        self.gh.check_runs = [{'id': i, 'name': rule['context'], 'head_sha': HEAD,
                              'status': 'completed', 'conclusion': 'success',
                              'app': {'id': 15368}}
                             for i, rule in enumerate(requirements, 1)]
        kernel = next(check for check in self.gh.check_runs if check['name'] == KERNEL_CHECK)
        # GitHub reports the job as success even though these build steps were skipped.
        # The gate consumes that check result, not the job's optional artifact or step list.
        kernel['output'] = {'summary': 'Kernel build skipped: only research notes, tables and standalone verifiers changed.'}
        self.assertTrue(gate.required_checks_passed(self.gh, HEAD, requirements))
        for status, conclusion in [('completed', 'failure'), ('in_progress', None),
                                   ('completed', 'skipped')]:
            with self.subTest(status=status, conclusion=conclusion):
                kernel.update(status=status, conclusion=conclusion)
                self.assertFalse(gate.required_checks_passed(self.gh, HEAD, requirements))
        self.gh.check_runs.remove(kernel)
        self.assertFalse(gate.required_checks_passed(self.gh, HEAD, requirements))


if __name__ == '__main__':
    unittest.main()
