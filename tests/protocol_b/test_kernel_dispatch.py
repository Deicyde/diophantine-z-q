"""Offline dispatch/provenance/recovery checks; no API or candidate code runs."""
import copy
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from urllib.parse import parse_qs, urlsplit
from test_gate import gate, FakeGH, HEAD, BASE, ROOT, changed, workflow


class KernelGH(FakeGH):
    def __init__(self):
        super().__init__()
        self.pr['base']['repo'] = {'full_name': self.repo}
        self.pr['head']['repo'] = {'full_name': 'fork/project'}
        self.kernel_text = (ROOT / '.github/workflows/kernel-lean.yml').read_text(encoding='utf-8')
        self.contract = json.dumps({'files': {'ZInQKernel/Example.lean': 'hash'}})
        self.root_entries = {ref: {name: {'path': name, 'mode': '040000', 'type': 'tree', 'sha': 'c'*40}
                                  for name in ('scripts', 'tests', '.github')} for ref in (BASE, HEAD)}
        self.refs, self.runs, self.artifacts = {}, [], {}
        self.writes, self.deletions = [], []
        self.create_error, self.dispatch_error, self.after_create = None, None, None

    def text(self, path, ref):
        if path == gate.LEAN_WORKFLOW:
            return self.kernel_text
        if path == 'KERNEL_CONTRACT.json':
            return self.contract
        return super().text(path, ref)

    def run(self, ident=44, **extra):
        return {'id': ident, 'run_attempt': 1, 'event': 'workflow_dispatch', 'head_sha': HEAD,
                'head_branch': gate.kernel_claim_ref(self.pr).removeprefix('refs/heads/'),
                'path': gate.LEAN_WORKFLOW, 'repository': {'full_name': self.repo},
                'head_repository': {'full_name': self.repo}, 'pull_requests': [],
                'status': 'completed', 'conclusion': 'success',
                'html_url': f'https://github.com/{self.repo}/actions/runs/{ident}', **extra}

    def ref(self, name=None, sha=HEAD):
        name = name or gate.kernel_claim_ref(self.pr)
        return {'ref': name, 'object': {'type': 'commit', 'sha': sha}}

    def call(self, path, method='GET', data=None):
        if path.startswith('/git/commits/'):
            ref = path.rsplit('/', 1)[1]
            return {'sha': ref, 'tree': {'sha': ref}}
        if path.startswith('/git/trees/'):
            ref = path.rsplit('/', 1)[1]
            return {'truncated': False, 'tree': list(self.root_entries[ref].values())}
        if path.startswith('/git/matching-refs/'):
            return list(self.refs.values())
        if path.startswith('/git/ref/'):
            ref = 'refs/' + path.removeprefix('/git/ref/')
            if ref not in self.refs:
                raise gate.RequestError({'status': 404})
            return copy.deepcopy(self.refs[ref])
        if path == '/git/refs' and method == 'POST':
            self.writes.append((path, method, data))
            ref = self.ref(data['ref'], data['sha'])
            self.refs[data['ref']] = ref
            if self.after_create:
                self.after_create()
            if self.create_error:
                raise self.create_error
            return copy.deepcopy(ref)
        if path.startswith('/git/refs/') and method == 'DELETE':
            ref = 'refs/' + path.removeprefix('/git/refs/')
            self.deletions.append(ref)
            del self.refs[ref]
            return None
        if path.startswith('/actions/workflows/kernel-lean.yml/runs?'):
            query = parse_qs(urlsplit(path).query)
            rows = [r for r in self.runs if
                    ('head_sha' not in query or r['head_sha'] == query['head_sha'][0]) and
                    ('branch' not in query or r['head_branch'] == query['branch'][0])]
            page = int(query.get('page', ['1'])[0])
            return {'total_count': len(rows), 'workflow_runs': copy.deepcopy(rows[(page-1)*100:page*100])}
        if path.startswith('/actions/runs/') and '/artifacts?' in path:
            ident = int(path.split('/')[3])
            return {'total_count': len(self.artifacts.get(ident, [])), 'artifacts': self.artifacts.get(ident, [])}
        if path.startswith('/actions/runs/'):
            ident = int(path.split('/')[3])
            return copy.deepcopy(next(r for r in self.runs if r['id'] == ident))
        return super().call(path, method, data)

    def dispatch_workflow(self, name, ref):
        self.dispatches.append((name, ref))
        ident = 100 + len(self.dispatches)
        self.runs.append(self.run(ident, head_branch=ref, status='queued', conclusion=None))
        if self.dispatch_error:
            raise self.dispatch_error
        return {'workflow_run_id': ident}


class KernelDispatch(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.patch = patch.object(gate, 'OUT', Path(self.tmp.name))
        self.patch.start()

    def tearDown(self):
        self.patch.stop()
        self.tmp.cleanup()

    def test_gate_pin_matches_cache_restricted_workflow(self):
        kernel = (ROOT / '.github/workflows/kernel-lean.yml').read_text(encoding='utf-8')
        self.assertEqual(gate.LEAN_WORKFLOW_SHA256, hashlib.sha256(kernel.encode()).hexdigest())
        self.assertIn("if: steps.cache_ref.outputs.is_main == 'true' && (steps.scope.outcome != 'success' || steps.scope.outputs.full_build != 'false')", kernel)

    def test_existing_direct_run_cannot_bypass_old_cache_workflow_rejection(self):
        for branch in ['Main', 'MAIN', 'contributor-branch']:
            for legacy_guard in ["github.ref == 'refs/heads/main'", 'true']:
                gh = KernelGH()
                gh.runs = [gh.run(head_branch=branch)]
                gh.kernel_text = gh.kernel_text.replace(
                    "steps.cache_ref.outputs.is_main == 'true'", legacy_guard)
                with self.subTest(branch=branch, legacy_guard=legacy_guard):
                    with self.assertRaisesRegex(ValueError, 'dispatch configuration'):
                        gate.ensure_kernel_dispatch(gh, gh.pr)
                    self.assertFalse(gh.writes)
                    self.assertFalse(gh.dispatches)

    def test_workflow_and_all_helper_trees_must_match_protected_base(self):
        for prefix in ('scripts', 'tests', '.github'):
            gh = KernelGH()
            gh.root_entries[HEAD][prefix]['sha'] = 'd'*40
            with self.subTest(prefix=prefix), self.assertRaisesRegex(ValueError, 'helper inputs'):
                gate.ensure_kernel_dispatch(gh, copy.deepcopy(gh.pr))
            self.assertFalse(gh.writes)
            self.assertFalse(gh.dispatches)
        gh = KernelGH(); gh.kernel_text += '\n# changed configuration\n'
        with self.assertRaisesRegex(ValueError, 'dispatch configuration'):
            gate.ensure_kernel_dispatch(gh, gh.pr)
        self.assertFalse(gh.writes)

    def test_foreign_or_stale_base_and_incomplete_tree_never_dispatch(self):
        for change in ('base_ref', 'base_repo', 'base_tip', 'behind', 'tree'):
            gh = KernelGH()
            if change == 'base_ref': gh.pr['base']['ref'] = 'other'
            if change == 'base_repo': gh.pr['base']['repo']['full_name'] = 'foreign/repo'
            if change == 'base_tip': gh.main_sha = 'd'*40
            if change == 'behind': gh.comparison['behind_by'] = 1
            if change == 'tree':
                original = gh.call
                gh.call = lambda p,*a,**k: {'truncated': True, 'tree': []} if p.startswith('/git/trees/') else original(p,*a,**k)
            with self.subTest(change=change), self.assertRaises(ValueError):
                gate.ensure_kernel_dispatch(gh, copy.deepcopy(gh.pr))
            self.assertFalse(gh.writes)
            self.assertFalse(gh.dispatches)

    def test_fork_gets_one_exact_head_dispatch_and_existing_run_is_reused(self):
        gh = KernelGH(); pr = copy.deepcopy(gh.pr)
        result = gate.ensure_kernel_dispatch(gh, pr)
        self.assertEqual(result['dispatched_run'], 101)
        self.assertEqual(gh.refs[gate.kernel_claim_ref(pr)]['object']['sha'], HEAD)
        self.assertEqual(gh.dispatches, [('kernel-lean.yml', gate.kernel_claim_ref(pr).removeprefix('refs/heads/'))])
        self.assertEqual(gate.ensure_kernel_dispatch(gh, pr), {'reused_run': 101})
        self.assertEqual(len(gh.dispatches), 1)
        record = json.loads((gate.OUT/'lean-kernel-dispatch-response.json').read_text())
        self.assertEqual(record['workflow_run_id'], 101)

    def test_existing_claim_without_visible_run_is_never_replayed_or_moved(self):
        gh = KernelGH(); ref = gate.kernel_claim_ref(gh.pr)
        gh.refs[ref] = gh.ref()
        for _ in range(2):
            self.assertEqual(gate.ensure_kernel_dispatch(gh, gh.pr), {'pending_claim': ref})
        self.assertFalse(gh.writes)
        self.assertFalse(gh.dispatches)
        gh.refs[ref]['object']['sha'] = 'd'*40
        with self.assertRaisesRegex(ValueError, 'never move'):
            gate.ensure_kernel_dispatch(gh, gh.pr)
        self.assertFalse(gh.writes)

    def test_dispatch_receipt_is_confirmed_by_exact_run_without_replaying(self):
        gh = KernelGH(); pr = copy.deepcopy(gh.pr)
        receipt = gate.ensure_kernel_dispatch(gh, pr)
        self.assertTrue(gate.confirm_kernel_dispatch(gh, pr, receipt))
        value = json.loads((gate.OUT/'lean-kernel-confirmed-run.json').read_text())
        self.assertEqual(value['id'], receipt['dispatched_run'])
        self.assertEqual(value['head_sha'], HEAD)
        for field, wrong in [('head_sha', 'e'*40), ('head_branch', 'main'), ('event', 'pull_request')]:
            original = gh.runs[0][field]; gh.runs[0][field] = wrong
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'identity mismatch'):
                gate.confirm_kernel_dispatch(gh, pr, receipt)
            gh.runs[0][field] = original
        with patch.object(gh, 'call', side_effect=gate.RequestError({'status':404})):
            self.assertFalse(gate.confirm_kernel_dispatch(gh, pr, receipt))
        self.assertEqual(len(gh.dispatches), 1)

    def test_uncertain_create_and_dispatch_do_not_repeat_the_write(self):
        for phase in ('create', 'dispatch'):
            gh = KernelGH(); pr = copy.deepcopy(gh.pr)
            setattr(gh, phase+'_error', RuntimeError('response lost after write'))
            with self.subTest(phase=phase), self.assertRaises(RuntimeError):
                gate.ensure_kernel_dispatch(gh, pr)
            counts = len(gh.writes), len(gh.dispatches)
            # Also simulate eventual consistency hiding an acknowledged/started run.
            gh.runs = []
            gate.ensure_kernel_dispatch(gh, pr)
            self.assertEqual((len(gh.writes), len(gh.dispatches)), counts)

    def test_changed_pr_after_claim_is_not_dispatched(self):
        gh = KernelGH(); pr = copy.deepcopy(gh.pr)
        gh.after_create = lambda: gh.pr['head'].update(sha='d'*40)
        with self.assertRaisesRegex(ValueError, 'changed after kernel claim'):
            gate.ensure_kernel_dispatch(gh, pr)
        self.assertFalse(gh.dispatches)

    def test_invalid_claim_identity_cannot_address_real_branches(self):
        for number in ('../main', 0, True):
            gh = KernelGH(); gh.pr['number'] = number
            with self.assertRaises(ValueError): gate.kernel_claim_ref(gh.pr)

    def test_newer_foreign_pr_run_does_not_override_direct_run_selection(self):
        gh = KernelGH()
        direct = gh.run(44)
        foreign = gh.run(99, event='pull_request', pull_requests=[{'number': 2, 'base': {'sha': 'e'*40}}])
        gh.runs = [direct, foreign]
        self.assertEqual([r['id'] for r in gate.direct_kernel_runs(gh, HEAD)], [44])
        self.assertFalse(gate.direct_kernel_run(gh, HEAD, gh.run(head_sha='e'*40)))
        self.assertFalse(gate.direct_kernel_run(gh, HEAD, gh.run(head_repository={'full_name': 'foreign/repo'})))

    def test_cleanup_waits_for_closed_pr_and_terminal_run_then_deletes_only_reserved_ref(self):
        gh = KernelGH(); ref = gate.kernel_claim_ref(gh.pr)
        gh.refs[ref] = gh.ref()
        gh.refs['refs/heads/main'] = gh.ref('refs/heads/main')
        gh.runs = [gh.run(status='in_progress', conclusion=None)]
        gate.cleanup_kernel_refs(gh)
        self.assertFalse(gh.deletions)
        gh.pr['state'] = 'closed'
        gate.cleanup_kernel_refs(gh)
        self.assertFalse(gh.deletions)
        gh.runs[0].update(status='completed', conclusion='success')
        gate.cleanup_kernel_refs(gh)
        self.assertEqual(gh.deletions, [ref])
        self.assertIn('refs/heads/main', gh.refs)
        # A reopened PR reuses the server's retained execution, not a second dispatch.
        gh.pr['state'] = 'open'
        self.assertEqual(gate.ensure_kernel_dispatch(gh, gh.pr), {'reused_run': 44})
        self.assertFalse(gh.dispatches)

    def test_cleanup_retains_missing_run_changed_ref_and_wrong_run_identity(self):
        for case in ('no_run', 'moved', 'wrong_run'):
            gh = KernelGH(); ref = gate.kernel_claim_ref(gh.pr)
            gh.pr['state'] = 'closed'; gh.refs[ref] = gh.ref()
            if case == 'moved': gh.refs[ref]['object']['sha'] = 'd'*40
            if case == 'wrong_run': gh.runs = [gh.run(head_sha='d'*40)]
            with self.subTest(case=case): gate.cleanup_kernel_refs(gh)
            self.assertFalse(gh.deletions)

    def test_preflight_and_cleanup_jobs_have_no_provider_environment(self):
        pre = workflow.split('  kernel_preflight:',1)[1].split('  run_reviewers:',1)[0]
        cleanup = workflow.split('  cleanup_kernel_refs:',1)[1]
        for block in (pre, cleanup):
            self.assertNotIn('environment: protocol-b', block)
            self.assertNotIn('secrets.', block)
        self.assertIn('needs: kernel_preflight', workflow)
        self.assertIn("github.event_name != 'schedule' && github.event.action != 'closed'", pre)
        self.assertNotIn('workflow_run:', workflow)
        self.assertIn("cron: '17 * * * *'", workflow)


if __name__ == '__main__': unittest.main()
