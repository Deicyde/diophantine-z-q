"""Exercise the production routing, admission and receipt entry points offline."""
import copy
from contextlib import ExitStack
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

import test_gate as tg
from test_gate import gate, HEAD, BASE, APP_ID
from test_outside_admission import candidate, response
from test_outside_screen import file, NOW, reservation


def runtime_env(directory):
    event = Path(directory)/'event.json'
    event.write_text(json.dumps({'pull_request': {'number': 20}}))
    return {'MODE': 'live', 'APP_ID': str(APP_ID), 'GITHUB_REPOSITORY': 'x/y',
            'GITHUB_SHA': BASE, 'GITHUB_REF': 'refs/heads/main',
            'GITHUB_EVENT_PATH': str(event), 'GITHUB_EVENT_NAME': 'pull_request_target',
            'GITHUB_RUN_ID': '7', 'GITHUB_RUN_ATTEMPT': '1', 'ROUTED_PR': '20',
            'GH_TOKEN': 'fixture', 'GITHUB_OUTPUT': str(Path(directory)/'outputs')}


class Runtime(unittest.TestCase):
    def test_job_boundaries_and_same_run_handoff_are_explicit(self):
        admission = tg.workflow.split('  outside_admission:\n', 1)[1].split('  kernel_preflight:\n', 1)[0]
        kernel = tg.workflow.split('  kernel_preflight:\n', 1)[1].split('  run_reviewers:\n', 1)[0]
        self.assertIn('group: protocol-b-outside-admission', admission)
        self.assertIn('cancel-in-progress: false', admission)
        self.assertIn('OPENAI_API_KEY:', admission)
        self.assertNotIn('ANTHROPIC_API_KEY:', admission)
        self.assertIn('app_id: ${{ steps.admit.outputs.app_id }}', admission)
        self.assertIn('APP_ID: ${{ needs.outside_admission.outputs.app_id }}', kernel)
        self.assertNotIn('environment:', kernel)
        self.assertNotIn('secrets.', kernel)
        self.assertIn('protocol-b-outside-${{ github.run_id }}-${{ github.run_attempt }}', kernel)
        self.assertNotIn('run-id:', kernel)

    def test_default_branch_and_current_policy_are_required(self):
        gh = Mock()
        gh.call.side_effect = lambda path: {'default_branch': 'main'} if path == '' else {'sha': BASE}
        for ref, policy in [('refs/heads/attacker', True), ('refs/heads/main', False)]:
            with self.subTest(ref=ref, policy=policy), patch.dict(os.environ, {'GITHUB_REF': ref, 'GITHUB_SHA': BASE}), \
                    patch.object(gate, 'same_policy', return_value=policy):
                with self.assertRaises(ValueError):
                    gate.outside_context(gh)

    def test_routes_collaborators_outside_authors_and_authorized_commands(self):
        for author_write, command, sender_write, eligible, outside in [
            (False, None, False, True, True), (True, None, False, True, False),
            (False, '/protocol-b review', True, True, False),
            (False, '/protocol-b review', False, False, False),
            (False, '/protocol-b merge '+HEAD, True, True, False),
            (False, 'unrelated', True, False, False)]:
            with self.subTest(command=command, author_write=author_write, sender_write=sender_write), \
                    tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
                env = runtime_env(directory)
                pr = candidate(); pr['base']['ref'] = 'main'
                event = {'pull_request': {'number': 20}}
                if command:
                    event = {'issue': {'number': 20}, 'sender': {'login': 'operator'},
                             'comment': {'body': command, 'user': {'login': 'operator'}}}
                Path(env['GITHUB_EVENT_PATH']).write_text(json.dumps(event))
                gh = Mock(); gh.call.return_value = pr
                stack.enter_context(patch.dict(os.environ, env))
                stack.enter_context(patch.object(gate, 'OUT', Path(directory)))
                stack.enter_context(patch.object(gate, 'GitHub', return_value=gh))
                stack.enter_context(patch.object(gate, 'outside_context', return_value='main'))
                stack.enter_context(patch.object(gate, 'collaborator', side_effect=lambda _, u:
                    sender_write if u['login'] == 'operator' else author_write))
                provider = stack.enter_context(patch.object(gate, 'outside_model_once'))
                gate.route_request()
                result = json.loads((Path(directory)/'request-route.json').read_text())
                self.assertEqual(result['eligible'], str(eligible).lower())
                self.assertEqual(result['outside'], str(outside).lower())
                provider.assert_not_called()

    def test_wakeup_recovers_unstarted_candidate_but_not_a_reserved_attempt(self):
        gh = Mock(repo='x/y')
        pr = candidate(); pr['base']['ref'] = 'main'
        comments = []
        gh.pages.side_effect = lambda path: [pr] if path.startswith('/pulls?') else comments
        gh.call.side_effect = lambda path: pr if path.startswith('/pulls/') else {
            'repository': {'full_name': 'x/y'}, 'status': 'completed',
            'path': '.github/workflows/research-checks.yml'}
        with patch.object(gate, 'collaborator', return_value=False), \
                patch.object(gate, 'outside_files', return_value=[file()]), \
                patch.object(gate, 'outside_computations_ready', return_value=True), \
                patch.object(gate, 'own_comment', return_value=True), \
                patch.dict(os.environ, {'MODE': 'live'}):
            self.assertEqual(gate.outside_wake_candidate(gh, 'main', {'workflow_run': {'id': 1}}), pr)
            comments.append({'body': gate.OUTSIDE_MARKER+'\noriginal intent'})
            self.assertIsNone(gate.outside_wake_candidate(gh, 'main', {}))
            gh.call.side_effect = lambda path: {'repository': {'full_name': 'outside/fork'},
                'status': 'completed', 'path': '.github/workflows/research-checks.yml'}
            self.assertIsNone(gate.outside_wake_candidate(gh, 'main', {'workflow_run': {'id': 1}}))

    def admission(self, *, files=None, ready=True, rows=None, existing=None, changed=False):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            stack.enter_context(patch.dict(os.environ, runtime_env(directory)))
            stack.enter_context(patch.object(gate, 'OUT', Path(directory)))
            gh, app = Mock(repo='x/y'), Mock(repo='x/y')
            pr = candidate(); pr['base']['ref'] = 'main'
            fresh = copy.deepcopy(pr)
            if changed: fresh['head']['sha'] = 'f'*40
            gh.call.side_effect = [pr, fresh, {'sha': BASE}]
            gh.pages.return_value = []
            stack.enter_context(patch.object(gate, 'start_clients', return_value=(gh, app)))
            stack.enter_context(patch.object(gate, 'outside_context', return_value='main'))
            stack.enter_context(patch.object(gate, 'collaborator', return_value=False))
            stack.enter_context(patch.object(gate, 'outside_existing_attempt', return_value=existing))
            stack.enter_context(patch.object(gate, 'outside_files', return_value=files or [file()]))
            stack.enter_context(patch.object(gate, 'outside_computations_ready', return_value=ready))
            stack.enter_context(patch.object(gate, 'same_policy', return_value=True))
            stack.enter_context(patch.object(gate, 'outside_reservations', return_value=rows or []))
            stack.enter_context(patch.object(gate, 'outside_reserve', return_value={'check': 201}))
            stack.enter_context(patch.object(gate, 'outside_update'))
            write = stack.enter_context(patch.object(gate, 'outside_api_once', return_value={
                'id': 200, 'app': {'id': APP_ID}}))
            provider = stack.enter_context(patch.object(gate, 'outside_model_once', return_value=response()))
            gate.admit_outside()
            outcome = json.loads((Path(directory)/'outside-admission.json').read_text())
            return outcome, provider.call_count, write.call_count

    def test_actual_admission_entry_point_spends_only_after_all_screens(self):
        for args, expected in [({'ready': False}, 'computations'),
                ({'files': [file('.github/bad.yml')]}, 'protected_path'),
                ({'rows': [reservation(1, pr=20)]}, 'quota')]:
            with self.subTest(args=args):
                result, calls, _ = self.admission(**args)
                self.assertEqual(calls, 0)
                self.assertFalse(result['full_review'])
                self.assertEqual(result['screen']['reason'], expected)
        result, calls, _ = self.admission(changed=True)
        self.assertFalse(result['full_review']); self.assertEqual(calls, 0)
        result, calls, _ = self.admission()
        self.assertTrue(result['full_review']); self.assertEqual(calls, 1)
        self.assertIn('quota_before', result)

    def test_duplicate_event_never_overwrites_existing_check(self):
        result, calls, writes = self.admission(existing={'stage': 'existing_attempt_retained'})
        self.assertEqual((calls, writes), (0, 0))
        self.assertFalse(result['full_review'])

    def test_earlier_reservation_cannot_authorize_a_second_round(self):
        pr = candidate()
        value = {'schema': gate.OUTSIDE_SCHEMA, 'intent': gate.outside_intent(pr, BASE, 7, 1),
                 'phase': 'review_started'}
        check = {'id': 201, 'name': gate.OUTSIDE_CHECK, 'app': {'id': APP_ID},
                 'output': {'text': json.dumps(value)}}
        with patch.object(gate, 'head_checks', return_value=[check]), \
                patch.object(gate, 'same_policy', return_value=True), \
                patch.dict(os.environ, {'GITHUB_SHA': BASE}):
            result = gate.outside_existing_attempt(Mock(), pr, APP_ID, gate.CHECK)
            self.assertEqual(result['phase'], 'review_started')
            self.assertNotIn('full_review', result)
            with patch.object(gate, 'same_policy', return_value=False):
                with self.assertRaises(ValueError):
                    gate.outside_existing_attempt(Mock(), pr, APP_ID, gate.CHECK)

    def test_completed_review_retains_history_validation_before_skipping(self):
        reports = {'astra': tg.envelope()}
        check = {'id': 201, 'name': gate.CHECK, 'app': {'id': APP_ID},
                 'output': {'text': json.dumps({'schema': 'protocol-b-decisions/v1', 'reports': reports})}}
        with ExitStack() as stack:
            stack.enter_context(patch.dict(os.environ, {'GITHUB_SHA': BASE}))
            stack.enter_context(patch.object(gate, 'head_checks', return_value=[check]))
            stack.enter_context(patch.object(gate, 'same_policy', return_value=True))
            stack.enter_context(patch.object(gate, 'review_spend_history', return_value={'candidates': []}))
            stack.enter_context(patch.object(gate, 'reconcile_obligations', return_value={}))
            stack.enter_context(patch.object(gate, 'history', return_value=([], {}, {}, None)))
            stack.enter_context(patch.object(gate, 'unaddressed_findings', return_value=False))
            pending = stack.enter_context(patch.object(gate, 'uncovered_history', return_value=False))
            result = gate.outside_existing_attempt(Mock(), candidate(), APP_ID, gate.CHECK)
            self.assertEqual(result['stage'], 'completed_review_retained')
            pending.return_value = True
            with self.assertRaisesRegex(ValueError, 'history has changed'):
                gate.outside_existing_attempt(Mock(), candidate(), APP_ID, gate.CHECK)

    def test_outside_editorial_change_still_uses_both_reviewers(self):
        gh = tg.FakeGH(); gh.author_permission = 'read'
        families = []
        with patch.object(gate, 'outside_receipt', return_value={'check': 201}), \
                patch.object(gate, 'classify', return_value='editorial'):
            _, _, _, state = tg.run_pipeline(gh=gh, finalize=False,
                provider=lambda reviewer: families.append(reviewer.family) or tg.report())
        self.assertEqual(set(families), set(gate.MODELS))
        self.assertEqual(state['outside_admission']['check'], 201)

    def test_pending_computations_stop_each_provider_before_its_request(self):
        for family in gate.MODELS:
            gh = tg.FakeGH()
            review = gate.Review(gh, gh.pr, [], [], {}, {}, 'instructions', family, 'local mathematical')
            review.input['outside_admission'] = {'check': 201}
            with self.subTest(family=family), tempfile.TemporaryDirectory() as directory, \
                    patch.object(gate, 'OUT', Path(directory)), \
                    patch.object(gate, 'outside_computations_ready', return_value=False), \
                    patch.object(gate, 'request') as request:
                with self.assertRaisesRegex(RuntimeError, 'computations must still pass'):
                    review.run()
                request.assert_not_called()


class Receipt(unittest.TestCase):
    def fixture(self, directory):
        pr = candidate()
        intent = gate.outside_intent(pr, BASE, 7, 1)
        value = {'schema': gate.OUTSIDE_SCHEMA, 'intent': intent, 'phase': 'ready_for_review',
                 'pointer_comment': 101, 'created_at': '2026-11-17T08:30:00Z',
                 'result': {'full_review': True, 'triage': {'decision': 'pass', 'category': 'docs'}}}
        check = {'id': 201, 'name': gate.OUTSIDE_CHECK, 'head_sha': HEAD, 'app': {'id': APP_ID},
                 'output': {'text': json.dumps(value)}}
        pointer = {'body': gate.outside_intent_body(intent), 'created_at': value['created_at'],
                   'updated_at': value['created_at'], 'issue_url': 'https://api.github.com/repos/x/y/issues/20'}
        local = {'reservation': {'check': 201}, 'full_review': True, 'quota_before': {'pr_attempts': 0}}
        (Path(directory)/'outside-admission.json').write_text(json.dumps(local))
        gh = Mock(repo='x/y')
        gh.call.side_effect = lambda path: check if path.startswith('/check-runs/') else pointer
        return pr, check, pointer, value, gh

    def test_receipt_binds_app_head_base_policy_run_attempt_and_immutable_pointer(self):
        mutations = [None, 'app', 'head', 'base', 'policy', 'run', 'attempt', 'phase', 'edited', 'other_pr']
        for mutation in mutations:
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
                pr, check, pointer, value, gh = self.fixture(directory)
                stack.enter_context(patch.dict(os.environ, runtime_env(directory)))
                stack.enter_context(patch.object(gate, 'OUT', Path(directory)))
                stack.enter_context(patch.object(gate, 'own_comment', return_value=True))
                if mutation == 'app': check['app'] = None
                elif mutation == 'head': check['head_sha'] = 'f'*40
                elif mutation in {'base', 'policy'}: value['intent'][mutation] = 'f'*40
                elif mutation in {'run', 'attempt'}: value['intent'][mutation] = '2'
                elif mutation == 'phase': value['phase'] = 'review_started'
                elif mutation == 'edited': pointer['updated_at'] = '2026-11-17T09:00:00Z'
                elif mutation == 'other_pr': pointer['issue_url'] += '1'
                check['output']['text'] = json.dumps(value)
                if mutation:
                    with self.assertRaises(ValueError): gate.outside_receipt(gh, pr)
                else:
                    update = stack.enter_context(patch.object(gate, 'outside_update'))
                    stack.enter_context(patch.object(gate, 'start_clients', return_value=(gh, gh)))
                    result = gate.outside_receipt(gh, pr, consume=True)
                    self.assertEqual(result['check'], 201)
                    self.assertEqual(update.call_args.args[2], 'review_started')

    def test_completion_preserves_actual_usage_and_rejects_another_attempt(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            pr, check, _, value, gh = self.fixture(directory)
            value['phase'] = 'review_started'; check['output']['text'] = json.dumps(value)
            stack.enter_context(patch.dict(os.environ, runtime_env(directory)))
            stack.enter_context(patch.object(gate, 'OUT', Path(directory)))
            update = stack.enter_context(patch.object(gate, 'outside_update'))
            (Path(directory)/'astra-turns.json').write_text(json.dumps([
                {'usage': {'input_tokens': 11, 'input_tokens_details': {'cached_tokens': 3}}},
                {'usage': {'input_tokens': 15, 'input_tokens_details': {'cached_tokens': 7}}}]))
            state = {'number': 20, 'head': HEAD, 'policy_ref': BASE, 'check': 202,
                     'conclusion': 'failure', 'outside_admission': {'check': 201}}
            gate.outside_finish(gh, gh, state)
            counts = state['outside_admission']['provider_usage']['astra']['reported_counter_sums']
            self.assertEqual(counts, {'input_tokens': 26, 'input_tokens_details.cached_tokens': 10})
            self.assertEqual(update.call_args.args[2], 'complete')
            with patch.dict(os.environ, {'GITHUB_RUN_ATTEMPT': '2'}):
                with self.assertRaises(ValueError): gate.outside_finish(gh, gh, state)

    def test_merge_command_requires_current_actual_app_acceptance(self):
        for change in [None, 'failure', 'app', 'head', 'policy']:
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
                stack.enter_context(patch.dict(os.environ, runtime_env(directory)))
                stack.enter_context(patch.object(gate, 'OUT', Path(directory)))
                value = {'schema': 'protocol-b-decisions/v1', 'number': 20, 'head': HEAD, 'policy_ref': BASE}
                check = {'id': 202, 'name': gate.CHECK, 'app': {'id': APP_ID},
                         'status': 'completed', 'conclusion': 'success'}
                if change == 'failure': check['conclusion'] = 'failure'
                if change == 'app': check['app'] = None
                if change == 'head': value['head'] = 'f'*40
                check['output'] = {'text': json.dumps(value)}
                stack.enter_context(patch.object(gate, 'head_checks', return_value=[check]))
                stack.enter_context(patch.object(gate, 'same_policy', return_value=change != 'policy'))
                merge = stack.enter_context(patch.object(gate, 'merge_and_dispatch'))
                provider = stack.enter_context(patch.object(gate, 'outside_model_once'))
                if change:
                    with self.assertRaises(ValueError): gate.outside_merge_command(Mock(), candidate(), 'main', 'live')
                    merge.assert_not_called()
                else:
                    gate.outside_merge_command(Mock(), candidate(), 'main', 'live')
                    merge.assert_called_once()
                provider.assert_not_called()


if __name__ == '__main__':
    unittest.main()
