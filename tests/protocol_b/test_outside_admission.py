"""Test the actual embedded admission code; no network or provider requests."""
import copy
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch
from test_gate import gate, HEAD, BASE, APP_ID
from test_gate import FakeGH, comment
import test_gate as tg
from test_outside_screen import NOW, file, pr, reservation


def candidate():
    value = pr()
    value.update(state='open', draft=False, head={'sha': HEAD}, base={'sha': BASE},
                 updated_at='2026-11-17T08:00:00Z')
    return value


def response(decision='pass', category='docs', reason='none'):
    value = {'decision': decision, 'category': category, 'reason': reason,
             'explanation': 'A specific finding from the supplied diff.'}
    return {'id': 'response-fixture', 'model': gate.MODELS['astra'], 'status': 'completed',
            'usage': {'input_tokens': 100, 'output_tokens': 30},
            'output': [{'type': 'message', 'content': [{'type': 'output_text', 'text': json.dumps(value)}]}]}


class Ledger:
    repo = 'x/y'

    def __init__(self):
        self.pr = candidate()
        self.pulls = [self.pr]
        self.comments = {self.pr['number']: []}
        self.checks = []
        self.calls = []
        self.lost_check_response = False
        self.lost_pointer_response = False

    def pages(self, path):
        if path.startswith('/pulls?'):
            return copy.deepcopy(self.pulls)
        if path.startswith('/issues/'):
            return copy.deepcopy(self.comments.get(int(path.split('/')[2]), []))
        raise AssertionError(path)

    def call(self, path):
        if path.startswith('/commits/'):
            rows = [r for r in self.checks if r['head_sha'] == path.split('/')[2]]
            return {'check_runs': copy.deepcopy(rows), 'total_count': len(rows)}
        raise AssertionError(path)

    def once(self, client, path, method, data):
        self.calls.append((path, method))
        if path.startswith('/issues/'):
            number = int(path.split('/')[2])
            row = {'id': 101+sum(map(len, self.comments.values())), 'body': data['body'],
                   'created_at': '2026-11-17T08:30:00Z', 'updated_at': '2026-11-17T08:30:00Z',
                   'user': {'login': 'github-actions[bot]'}}
            self.comments.setdefault(number, []).append(row)
            if self.lost_pointer_response:
                raise TimeoutError('Response lost after write')
            return copy.deepcopy(row)
        if path == '/check-runs':
            row = {'id': 201+len(self.checks), 'app': {'id': APP_ID}, **data}
            self.checks.append(row)
            if self.lost_check_response:
                raise TimeoutError('Response lost after write')
            return copy.deepcopy(row)
        raise AssertionError(path)

    def reserve(self):
        return gate.outside_reserve(self, self, self.pr, BASE, 7, 1, APP_ID, self.once)

    def read(self):
        return gate.outside_reservations(self, self, self.pr, NOW, APP_ID)


class ReservationTests(unittest.TestCase):
    def test_effective_requests_are_never_retried_and_do_not_follow_redirects(self):
        opener = Mock()
        opener.open.side_effect = TimeoutError('secret token must not appear')
        with patch.object(gate.urllib.request, 'build_opener', return_value=opener) as factory:
            with self.assertRaisesRegex(RuntimeError, 'reconcile its durable intent') as failure:
                gate.outside_json_once('https://api.github.com/repos/x/y/check-runs',
                                       {'Authorization': 'Bearer fixture'}, 'POST', {})
            opener.open.assert_called_once()
            self.assertNotIn('secret', str(failure.exception))
            redirect = factory.call_args.args[0]()
            self.assertIsNone(redirect.redirect_request(None, None, 302, '', {}, 'https://other.invalid'))

    def test_single_request_limits_response_and_requires_json_object(self):
        for payload in (b'x'*2_000_001, b'[]', b'{invalid'):
            opener = Mock()
            opener.open.return_value = io.BytesIO(payload)
            with patch.object(gate.urllib.request, 'build_opener', return_value=opener):
                with self.assertRaises(RuntimeError):
                    gate.outside_json_once('https://api.github.com/repos/x/y/check-runs', {}, 'POST', {})
            opener.open.assert_called_once()

    def test_triage_uses_only_fixed_provider_and_missing_key_sends_nothing(self):
        with patch.dict(os.environ, {'OPENAI_API_KEY': ''}), patch.object(gate, 'outside_json_once') as send:
            with self.assertRaisesRegex(ValueError, 'No triage API credential'):
                gate.outside_model_once({})
            send.assert_not_called()
        with patch.dict(os.environ, {'OPENAI_API_KEY': 'fixture'}), patch.object(gate, 'outside_json_once') as send:
            gate.outside_model_once({'model': gate.MODELS['astra']})
            self.assertEqual(send.call_args.args[0], 'https://api.openai.com/v1/responses')
            self.assertEqual(send.call_args.kwargs['timeout'], 180)

    def test_app_record_binds_head_author_pointer_and_server_timestamp(self):
        ledger = Ledger()
        slot = ledger.reserve()
        self.assertEqual([x[0] for x in ledger.calls], ['/issues/20/comments', '/check-runs'])
        self.assertEqual(slot['value']['intent']['head'], HEAD)
        self.assertEqual(ledger.read(), [{'check_id': 201, 'pr': 20, 'author_id': 7,
                                          'created_at': '2026-11-17T08:30:00Z'}])
        ledger.pr['user']['login'] = 'renamed-account'
        self.assertEqual(len(ledger.read()), 1)

    def test_lost_pointer_response_blocks_future_admission_without_a_model_call(self):
        ledger = Ledger()
        ledger.lost_pointer_response = True
        with self.assertRaises(TimeoutError):
            ledger.reserve()
        self.assertEqual(len(ledger.calls), 1)
        with self.assertRaisesRegex(ValueError, 'Uncertain unattended reservation'):
            ledger.read()

    def test_lost_check_response_is_recovered_as_an_already_reserved_slot(self):
        ledger = Ledger()
        ledger.lost_check_response = True
        with self.assertRaises(TimeoutError):
            ledger.reserve()
        self.assertEqual(len(ledger.calls), 2)
        rows = ledger.read()
        self.assertEqual(gate.outside_quota(ledger.pr, rows, NOW)[1], 'pr_attempts')

    def test_wrong_app_mismatched_head_edited_pointer_and_forged_author_fail_closed(self):
        for defect in ('app', 'head', 'edited', 'author', 'payload', 'duplicate'):
            with self.subTest(defect=defect):
                ledger = Ledger()
                ledger.reserve()
                row = ledger.checks[0]
                if defect == 'app': row['app']['id'] += 1
                if defect == 'head': row['head_sha'] = 'f'*40
                if defect == 'edited': ledger.comments[20][0]['updated_at'] = '2026-11-17T08:31:00Z'
                if defect == 'author': ledger.pr['user']['id'] += 1
                if defect == 'payload': row['output']['text'] = '{}'
                if defect == 'duplicate': ledger.checks.append({**copy.deepcopy(row), 'id': 999})
                with self.assertRaises(ValueError):
                    ledger.read()

    def test_outsider_comment_alone_neither_grants_a_slot_nor_counts_as_app_evidence(self):
        ledger = Ledger()
        ledger.reserve()
        ledger.comments[20][0]['user']['login'] = 'contributor'
        self.assertEqual(ledger.read(), [])

    def test_prior_force_pushed_head_is_still_counted(self):
        ledger = Ledger()
        ledger.reserve()
        ledger.pr['head']['sha'] = 'f'*40
        self.assertEqual(len(ledger.read()), 1)

    def test_phase_does_not_advance_on_an_unconfirmed_app_update(self):
        ledger = Ledger()
        slot = ledger.reserve()
        once = Mock(return_value={'id': slot['check'], 'app': {'id': 999}})
        with self.assertRaisesRegex(ValueError, 'not confirmed'):
            gate.outside_update(ledger, slot, 'triage_started', {}, APP_ID, once)
        self.assertEqual(slot['value']['phase'], 'reserved')

    def test_partial_or_changing_check_pages_refuse_admission(self):
        app = Mock()
        app.call.return_value = {'total_count': 1, 'check_runs': []}
        with self.assertRaisesRegex(ValueError, 'pagination incomplete'):
            gate.outside_checks(app, HEAD)
        app.call.side_effect = [{'total_count': 2, 'check_runs': [{'id': 1, 'head_sha': HEAD}]},
                               {'total_count': 3, 'check_runs': [{'id': 2, 'head_sha': HEAD}]}]
        with self.assertRaisesRegex(ValueError, 'changed or is incomplete'):
            gate.outside_checks(app, HEAD)


class AdmissionTests(unittest.TestCase):
    def test_required_computation_reader_rejects_pending_missing_failed_neutral_and_wrong_app(self):
        gh = tg.Checks().ready_gh()
        self.assertTrue(gate.outside_computations_ready(gh, gh.pr, 'main'))
        for defect in ('pending', 'missing', 'failure', 'neutral', 'app', 'rule'):
            gh = tg.Checks().ready_gh()
            target = next(row for row in gh.check_runs if row['name'] != gate.CHECK)
            if defect == 'pending': target.update(status='in_progress', conclusion=None)
            if defect == 'missing': gh.check_runs.remove(target)
            if defect in ('failure', 'neutral'): target['conclusion'] = defect
            if defect == 'app': target['app'] = None
            if defect == 'rule': gh.required.remove(target['name'])
            self.assertFalse(gate.outside_computations_ready(gh, gh.pr, 'main'), defect)

    def test_complete_lean_source_is_read_at_the_correct_revision(self):
        gh = Mock()
        p = candidate()
        for status, revision, key in [('modified', HEAD, 'content'), ('removed', BASE, 'previous_content')]:
            row = file('ZInQKernel/Contrib/X.lean')
            row.pop('content'); row.pop('previous_content')
            row['status'] = status
            gh.pages.return_value = [row]
            gh.text.return_value = 'theorem x : True := trivial'
            result = gate.outside_files(gh, p)
            self.assertEqual(result[0][key], gh.text.return_value)
            gh.text.assert_called_with(row['filename'], revision)

    def invoke(self, p=None, files=None, required=True, records=None, answer=None, fresh=None):
        p = p or candidate()
        self.reserve = Mock(return_value={'check': 201, 'value': {}})
        self.update = Mock()
        self.provider = Mock(return_value=answer or response())
        if isinstance(answer, Exception):
            self.provider.side_effect = answer
        return gate.outside_admit(p, files or [file()], required, records or [], NOW, [],
                                 reserve=self.reserve, update=self.update, provider=self.provider,
                                 refresh=Mock(return_value=fresh or (p, True, True)))

    def test_every_mechanical_refusal_makes_no_provider_request_or_reservation(self):
        cases = []
        cases.append({'files': [file('.github/workflows/untrusted.yml')]})
        f = file(); del f['patch']; cases.append({'files': [f]})
        p = candidate(); p['changed_files'] = 21
        cases.append({'p': p, 'files': [file(f'docs/{i}.md') for i in range(21)]})
        p = candidate(); p['body'] = 'Unfilled template'; cases.append({'p': p})
        cases.extend({'required': x} for x in (False, None, 'success'))
        cases.append({'records': [reservation(1, pr=20)]})
        cases.append({'files': [file('ZInQKernel/Contrib/X.lean', 'unsafe def x := 1')]})
        p = candidate(); p['changed_files'] = 4
        cases.append({'p': p, 'files': [file(f'ZInQKernel/Contrib/X{i}.lean') for i in range(4)]})
        p = candidate(); p['body'] += 'x'*32001; cases.append({'p': p})
        for case in cases:
            with self.subTest(case=case):
                result = self.invoke(**case)
                self.assertFalse(result['full_review'])
                self.provider.assert_not_called()
                self.reserve.assert_not_called()

    def test_deleted_comment_cannot_hide_unsafe_code_in_context_lines(self):
        f = file('ZInQKernel/Contrib/X.lean', 'theorem x : True := trivial', '/-')
        f['content'] = 'unsafe def latent := 0\ntheorem x : True := trivial'
        self.invoke(files=[f])
        self.provider.assert_not_called()
        for text in ('include_str "data"', 'include_bin "data"', 'readBinFile "data"'):
            self.invoke(files=[file('ZInQKernel/Contrib/X.lean', text)])
            self.provider.assert_not_called()
        for path in ('lean/lakefile.toml', 'vendor/a/lean-toolchain'):
            self.invoke(files=[file(path)])
            self.provider.assert_not_called()

    def test_head_base_author_policy_or_checks_change_after_reservation_stops_spending(self):
        for changed in ('head', 'base', 'author', 'draft', 'closed', 'checks', 'policy'):
            p = candidate(); fresh = copy.deepcopy(p)
            if changed in ('head', 'base'): fresh[changed]['sha'] = 'f'*40
            if changed == 'author': fresh['user']['id'] += 1
            if changed == 'draft': fresh['draft'] = True
            if changed == 'closed': fresh['state'] = 'closed'
            result = self.invoke(p=p, fresh=(fresh, changed != 'checks', changed != 'policy'))
            self.reserve.assert_called_once()
            self.provider.assert_not_called()
            self.assertFalse(result['full_review'])

    def test_all_categories_and_valid_uncertainty_preserve_merge_limits(self):
        for category in gate.OUTSIDE_CATEGORIES:
            path = 'research/note.md' if category == 'improvement_note' else 'docs/note.md'
            result = self.invoke(files=[file(path)], answer=response(category=category))
            self.provider.assert_called_once()
            self.assertTrue(result['full_review'])
            self.assertEqual(result['automatic_merge'], category in {'docs', 'improvement_note'})
            self.assertEqual([c.args[1] for c in self.update.call_args_list], ['triage_started', 'ready_for_review'])
        result = self.invoke(answer=response('needs_maintainer', reason='uncertain'))
        self.assertTrue(result['full_review'])
        self.assertFalse(result['automatic_merge'])

    def test_reject_or_unconfirmed_provider_does_not_start_full_review_or_retry(self):
        for rejection in gate.OUTSIDE_REJECTIONS:
            result = self.invoke(answer=response('reject', reason=rejection))
            self.assertFalse(result['full_review'])
            self.provider.assert_called_once()
        result = self.invoke(answer=TimeoutError('Uncertain provider response'))
        self.assertEqual(result['reason'], 'provider_request_unconfirmed')
        self.provider.assert_called_once()
        result = self.invoke(answer={'model': 'wrong'})
        self.assertEqual(result['reason'], 'invalid_triage')
        self.provider.assert_called_once()


class MergePermissionTests(unittest.TestCase):
    def setUp(self):
        self.ledger = Ledger()
        self.slot = self.ledger.reserve()
        pointer = self.ledger.comments[20][0]
        pointer['issue_url'] = 'https://api.github.com/repos/x/y/issues/20'
        value = json.loads(self.ledger.checks[0]['output']['text'])
        value.update(phase='review_started', result={
            'triage': {'decision': 'pass', 'category': 'docs'}, 'full_review': True})
        self.value = value
        self.state = {'head': HEAD, 'policy_ref': BASE, 'outside_admission': {'check': 201}}
        self.files = [file()]
        self.gh = Mock(repo='x/y')
        self.gh.call.side_effect = lambda path: (self.check() if path == '/check-runs/201'
                                                 else pointer if path == '/issues/comments/101'
                                                 else (_ for _ in ()).throw(AssertionError(path)))
        self.gh.pages.side_effect = lambda path: self.files if path.endswith('/files') else self.ledger.comments[20]

    def check(self):
        return {**self.ledger.checks[0], 'output': {'text': json.dumps(self.value)}}

    def decision(self, allowed_users=()):
        with patch.object(gate, 'collaborator', side_effect=lambda gh, user: user['login'] in allowed_users):
            return gate.outside_merge_permission(self.gh, self.state, self.ledger.pr, APP_ID)

    def test_collaborators_unchanged_and_outside_docs_need_authentic_receipt(self):
        self.assertTrue(self.decision(('contributor',))['allowed'])
        self.assertTrue(self.decision()['allowed'])
        self.ledger.checks[0]['app']['id'] = 15368
        self.assertFalse(self.decision()['allowed'])

    def test_all_categories_and_path_clamps_apply_after_acceptance(self):
        for category in gate.OUTSIDE_CATEGORIES:
            self.value['result']['triage']['category'] = category
            self.files = [file('research/note.md' if category == 'improvement_note' else 'docs/note.md')]
            self.assertEqual(self.decision()['allowed'], category in {'docs', 'improvement_note'})
            self.files = [file('.github/workflows/fake.yml')]
            self.assertFalse(self.decision()['allowed'])

    def test_unknown_unfinished_and_changed_bindings_are_not_merge_permission(self):
        original = copy.deepcopy(self.value)
        for key, replacement in [('phase', 'ready_for_review'), ('schema', 'fake')]:
            self.value = {**copy.deepcopy(original), key: replacement}
            self.assertFalse(self.decision()['allowed'])
        for key in ['head', 'base', 'policy']:
            self.value = copy.deepcopy(original)
            self.value['intent'][key] = 'f'*40
            self.assertFalse(self.decision()['allowed'])
        self.value = copy.deepcopy(original)
        self.value['result']['triage']['decision'] = 'needs_maintainer'
        self.assertFalse(self.decision()['allowed'])

    def test_only_unedited_current_collaborator_exact_head_merge_command_allows_manual_merge(self):
        self.state.pop('outside_admission')
        comment = {'id': 999, 'body': '/protocol-b merge '+HEAD,
                   'created_at': 'now', 'updated_at': 'now',
                   'user': {'login': 'maintainer', 'type': 'User'}}
        self.ledger.comments[20].append(comment)
        self.assertFalse(self.decision()['allowed'])
        self.assertTrue(self.decision(('maintainer',))['allowed'])
        comment['body'] = '/protocol-b review'
        self.assertFalse(self.decision(('maintainer',))['allowed'])
        comment['body'] = '/protocol-b merge '+'f'*40
        self.assertFalse(self.decision(('maintainer',))['allowed'])
        comment['body'] = '/protocol-b merge '+HEAD
        comment['updated_at'] = 'later'
        self.assertFalse(self.decision(('maintainer',))['allowed'])


class MergePathTests(unittest.TestCase):
    def run_merge(self, gh):
        with tempfile.TemporaryDirectory() as directory, patch.object(gate, 'OUT', Path(directory)), \
                patch.dict(os.environ, {'APP_ID': str(APP_ID)}):
            gate.merge_and_dispatch(gh, {'number': 1, 'head': HEAD, 'policy_ref': BASE, 'default': 'main'})

    def test_accepted_outside_review_alone_can_neither_merge_directly_nor_enable_auto_merge(self):
        for ready in (True, False):
            gh = tg.Checks().ready_gh() if ready else FakeGH()
            gh.author_permission = 'read'
            self.run_merge(gh)
            self.assertFalse(gh.merge_requests)
            self.assertIsNone(gh.graphql)
            self.assertFalse(gh.dispatches)

    def test_collaborator_merge_approval_is_checked_on_both_paths(self):
        for ready in (True, False):
            gh = tg.Checks().ready_gh() if ready else FakeGH()
            gh.author_permission, gh.permission = 'read', 'write'
            gh.comments.append(comment('/protocol-b merge '+HEAD, 'collaborator'))
            self.run_merge(gh)
            self.assertEqual(bool(gh.merge_requests), ready)
            self.assertEqual(gh.graphql is not None, not ready)


if __name__ == '__main__':
    unittest.main()
