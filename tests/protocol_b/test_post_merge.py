"""Regression tests for confirmed direct-merge dispatch and refusal recovery."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import test_gate as tg

MERGE = 'd' * 40
STATE = {'number': 1, 'head': tg.HEAD, 'default': 'main', 'policy_ref': tg.BASE}
REFUSAL = {'type': 'UNPROCESSABLE', 'message': 'Pull request Pull request is in unstable status'}


class PostMerge(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.out = Path(tmp.name)
        self.out_patch = patch.object(tg.gate, 'OUT', self.out)
        self.out_patch.start()
        self.addCleanup(self.out_patch.stop)

    def test_direct_merge_dispatches_both_on_main_without_inputs(self):
        gh = tg.Checks().ready_gh()
        _, _, errors, _ = tg.run_pipeline(gh, mode='live')
        self.assertEqual(errors, [])
        self.assertEqual(gh.dispatches, [('research-checks.yml', {'ref': 'main'}),
                                         ('kernel-lean.yml', {'ref': 'main'})])

    def test_deferred_auto_merge_does_not_poll_or_dispatch(self):
        for already_enabled in (False, True):
            gh = tg.FakeGH()
            if already_enabled:
                gh.pr['auto_merge'] = {'enabled': True}
            with patch.object(tg.gate.time, 'sleep', side_effect=AssertionError('No polling')):
                _, _, errors, _ = tg.run_pipeline(gh, mode='live')
            self.assertEqual(errors, [])
            self.assertEqual(gh.dispatches, [])
            self.assertFalse(gh.pr['merged'])

    def test_merge_and_actual_run_shas_are_recorded_even_if_main_advances(self):
        gh = tg.FakeGH()
        gh.complete_merge()
        gh.main_sha = gh.dispatch_head = 'e' * 40
        tg.gate.confirm_and_dispatch(gh, STATE, MERGE)
        for workflow in ('research-checks.yml', 'kernel-lean.yml'):
            receipt = json.loads((self.out / ('dispatch-' + workflow + '.json')).read_text())
            self.assertEqual(receipt['merge_commit_sha'], MERGE)
            self.assertEqual(receipt['head_sha'], 'e' * 40)
            self.assertTrue(receipt['head_differs_from_merge'])
            self.assertEqual(receipt['status'], 'run_confirmed')

    def test_dispatch_api_uses_run_id_returning_version_and_main_only(self):
        gh = tg.gate.GitHub('x/y', 'fake')
        with patch.object(tg.gate, 'request', return_value={'workflow_run_id': 123}) as request:
            self.assertEqual(gh.dispatch_workflow('kernel-lean.yml', 'main'), {'workflow_run_id': 123})
        args = request.call_args.args
        self.assertEqual(args[0], 'https://api.github.com/repos/x/y/actions/workflows/kernel-lean.yml/dispatches')
        self.assertEqual(args[1]['X-GitHub-Api-Version'], '2026-03-10')
        self.assertEqual(args[2:], ('POST', {'ref': 'main'}))

    def test_unconfirmed_closed_changed_or_invalid_merge_never_dispatches(self):
        cases = ['open', 'closed', 'head', 'base', 'invalid_sha', 'different_sha', 'not_on_main']
        for case in cases:
            with self.subTest(case=case):
                gh = tg.FakeGH()
                if case != 'open': gh.complete_merge()
                if case == 'closed': gh.pr['merged'] = False
                if case == 'head': gh.pr['head']['sha'] = 'c' * 40
                if case == 'base': gh.pr['base']['ref'] = 'other'
                if case == 'invalid_sha': gh.pr['merge_commit_sha'] = 'bad'
                if case == 'different_sha': gh.pr['merge_commit_sha'] = 'e' * 40
                if case == 'not_on_main': gh.comparison = {'behind_by': 1}
                with self.assertRaises(RuntimeError):
                    tg.gate.confirm_and_dispatch(gh, STATE, expected_merge=MERGE)
                self.assertEqual(gh.dispatches, [])

    def test_auto_refusal_rechecks_once_and_merges_newly_ready_head(self):
        gh = tg.Checks().ready_gh()
        gh.check_runs[0].update(status='in_progress', conclusion=None)
        gh.auto_result = {'data': None, 'errors': [REFUSAL]}
        def finish_ci(client):
            client.check_runs[0].update(status='completed', conclusion='success')
        gh.auto_callback = finish_ci
        _, _, errors, _ = tg.run_pipeline(gh, mode='live')
        self.assertEqual(errors, [])
        self.assertEqual(gh.rule_pages, [1, 1])
        self.assertEqual(gh.merge_requests, [{'sha': tg.HEAD, 'merge_method': 'merge'}])
        self.assertEqual(len(gh.dispatches), 2)

    def test_auto_refusal_rechecks_all_guards_without_repeating_request(self):
        for fault in ['pending', 'head', 'policy', 'rule', 'behind']:
            with self.subTest(fault=fault):
                gh = tg.Checks().ready_gh()
                gh.check_runs[0].update(status='in_progress', conclusion=None)
                gh.auto_result = {'data': None, 'errors': [REFUSAL]}
                calls = []
                def after_refusal(client):
                    calls.append(1)
                    if fault != 'pending': client.check_runs[0].update(status='completed', conclusion='success')
                    if fault == 'head': client.pr['head']['sha'] = 'e' * 40
                    if fault == 'policy':
                        client.main_sha = 'c' * 40
                        client.text = lambda path, ref: ref
                    if fault == 'rule': client.required = {tg.gate.CHECK}
                    if fault == 'behind': client.comparison = {'behind_by': 1}
                gh.auto_callback = after_refusal
                _, _, errors, _ = tg.run_pipeline(gh, mode='live')
                self.assertTrue(errors)
                self.assertEqual(calls, [1])
                self.assertEqual(gh.merge_requests, [])
                self.assertEqual(gh.dispatches, [])

    def test_uncertain_auto_response_does_not_fallback_or_dispatch(self):
        for error in [TimeoutError('unknown outcome'), tg.gate.RequestError({'status': 503})]:
            gh = tg.FakeGH()
            with patch.object(gh, 'api', side_effect=error):
                _, _, errors, _ = tg.run_pipeline(gh, mode='live')
            self.assertTrue(errors)
            self.assertEqual(gh.rule_pages, [1])
            self.assertEqual(gh.merge_requests, [])
            self.assertEqual(gh.dispatches, [])

    def test_partial_graphql_success_is_not_replayed(self):
        gh = tg.FakeGH()
        gh.auto_result['errors'] = [{'type': 'INTERNAL'}]
        _, _, errors, _ = tg.run_pipeline(gh, mode='live')
        self.assertTrue(any('Ambiguous' in e for e in errors))
        self.assertEqual(gh.rule_pages, [1])
        self.assertEqual(gh.merge_requests, [])

    def test_dispatch_failure_retains_intent_continues_other_workflow_and_never_retries(self):
        gh = tg.FakeGH()
        gh.complete_merge()
        original = gh.dispatch_workflow
        attempts = []
        def dispatch(workflow, ref):
            attempts.append(workflow)
            if workflow == 'research-checks.yml':
                raise TimeoutError('unknown dispatch outcome')
            return original(workflow, ref)
        gh.dispatch_workflow = dispatch
        with self.assertRaisesRegex(RuntimeError, 'needs reconciliation'):
            tg.gate.confirm_and_dispatch(gh, STATE, MERGE)
        self.assertEqual(attempts, ['research-checks.yml', 'kernel-lean.yml'])
        self.assertEqual(json.loads((self.out/'dispatch-research-checks.yml.json').read_text())['status'], 'intent')
        self.assertEqual(json.loads((self.out/'dispatch-kernel-lean.yml.json').read_text())['status'], 'run_confirmed')

    def test_dispatch_without_run_id_is_recorded_without_retry(self):
        gh = tg.FakeGH()
        gh.complete_merge()
        with patch.object(gh, 'dispatch_workflow', return_value=None) as dispatch:
            with self.assertRaisesRegex(RuntimeError, 'did not return a run ID'):
                tg.gate.confirm_and_dispatch(gh, STATE, MERGE)
        self.assertEqual(dispatch.call_count, 2)
        receipt = json.loads((self.out/'dispatch-research-checks.yml.json').read_text())
        self.assertEqual(receipt['status'], 'accepted')
        self.assertIn('error', receipt)

    def test_wrong_run_identity_fails_without_claiming_confirmed_run(self):
        for field, value in [('id', 42), ('head_sha', 'bad'), ('head_branch', 'other'),
                             ('event', 'push'), ('path', '.github/workflows/other.yml'),
                             ('path', '.github/workflows/research-checks.yml@other')]:
            with self.subTest(field=field):
                gh = tg.FakeGH()
                gh.complete_merge()
                original = gh.call
                def call(path, method='GET', data=None):
                    result = original(path, method, data)
                    if path.startswith('/actions/runs/'):
                        result[field] = value
                    return result
                gh.call = call
                with self.assertRaisesRegex(RuntimeError, 'Unexpected dispatched run identity'):
                    tg.gate.confirm_and_dispatch(gh, STATE, MERGE)
                self.assertEqual(len(gh.dispatches), 2)
                receipt = json.loads((self.out/'dispatch-research-checks.yml.json').read_text())
                self.assertEqual(receipt['status'], 'accepted')
                self.assertNotIn('head_differs_from_merge', receipt)

    def test_http_status_alone_never_triggers_fallback(self):
        for status in (400, 403, 422, 500):
            gh = tg.Checks().ready_gh()
            gh.check_runs[0].update(status='in_progress', conclusion=None)
            def refuse(*args):
                gh.check_runs[0].update(status='completed', conclusion='success')
                raise tg.gate.RequestError({'status': status})
            with patch.object(gh, 'api', side_effect=refuse) as mutation:
                _, _, errors, _ = tg.run_pipeline(gh, mode='live')
            self.assertTrue(errors)
            self.assertEqual(mutation.call_count, 1)
            self.assertEqual(gh.rule_pages, [1])
            self.assertEqual(gh.merge_requests, [])

    def test_null_graphql_execution_results_and_unknown_errors_never_retry(self):
        for data in (None, {}, {'enablePullRequestAutoMerge': None}):
            for issues in ([{'type': 'INTERNAL', 'message': 'execution failed'}],
                           [{'type': 'UNPROCESSABLE', 'message': 'unknown failure'}],
                           [REFUSAL, {'type': 'INTERNAL'}]):
                with self.subTest(data=data, errors=issues):
                    gh = tg.Checks().ready_gh()
                    gh.check_runs[0].update(status='in_progress', conclusion=None)
                    gh.auto_result = {'data': data, 'errors': issues}
                    def finish_ci(client):
                        client.check_runs[0].update(status='completed', conclusion='success')
                    gh.auto_callback = finish_ci
                    _, _, errors, _ = tg.run_pipeline(gh, mode='live')
                    self.assertTrue(errors)
                    self.assertEqual(gh.rule_pages, [1])
                    self.assertEqual(gh.merge_requests, [])
                    self.assertEqual(gh.dispatches, [])

    def test_known_clean_and_unstable_state_refusals_recheck_once(self):
        for message in ('Pull request is in clean status', 'Pull request is in unstable status',
                        'Pull request Pull request is in unstable status'):
            gh = tg.Checks().ready_gh()
            gh.check_runs[0].update(status='in_progress', conclusion=None)
            gh.auto_result = {'errors': [{'type': 'UNPROCESSABLE', 'message': message}]}
            def finish_ci(client):
                client.check_runs[0].update(status='completed', conclusion='success')
            gh.auto_callback = finish_ci
            _, _, errors, _ = tg.run_pipeline(gh, mode='live')
            self.assertEqual(errors, [])
            self.assertEqual(gh.rule_pages, [1, 1])
            self.assertEqual(len(gh.merge_requests), 1)

    def test_bare_and_main_qualified_workflow_paths_are_accepted(self):
        for suffix in ('', '@main'):
            gh = tg.FakeGH()
            gh.complete_merge()
            original = gh.call
            def call(path, method='GET', data=None):
                result = original(path, method, data)
                if path.startswith('/actions/runs/'):
                    result['path'] += suffix
                return result
            gh.call = call
            tg.gate.confirm_and_dispatch(gh, STATE, MERGE)
            self.assertEqual(len(gh.dispatches), 2)


if __name__ == '__main__':
    unittest.main()
