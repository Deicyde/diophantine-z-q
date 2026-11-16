import unittest
from unittest.mock import patch

from test_gate import gate, FakeGH, FakeApp, HEAD, envelope, report, comment, report_comment, run_pipeline


class AdminOverrides(unittest.TestCase):
    def setup_case(self, permission):
        gh, app = FakeGH(), FakeApp()
        gh.permission = permission
        pair = {'astra': envelope(review=report(decision='changes_requested', findings=[
                    {'id': 'F1', 'location': 'p:1', 'objection': 'A substantive finding'}])),
                'fable': envelope('fable')}
        app.prior(pair)
        command = comment('/protocol-b override '+HEAD+' 1-1-astra-F1 Owner decision', 'collaborator')
        gh.comments = [report_comment(e) for e in pair.values()]+[command]
        event = {'issue': {'number': 1}, 'comment': command, 'sender': {'login': 'collaborator'}}
        return gh, app, event

    def test_write_and_maintain_override_is_ignored_without_model_calls(self):
        for permission in ('write', 'maintain'):
            with self.subTest(permission=permission):
                gh, app, event = self.setup_case(permission)
                self.assertFalse(gate.history(gh, gh.pr)[2])
                with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call')):
                    _, app, errors, state = run_pipeline(gh, app, event=event,
                        provider=lambda _: (_ for _ in ()).throw(AssertionError('No review')))
                self.assertEqual(errors, [])
                self.assertIsNone(state)
                self.assertEqual(app.created, [])
                self.assertTrue(any('Only a repository admin' in p['body'] for p in gh.posts))

    def test_admin_override_still_works_without_model_calls(self):
        gh, app, event = self.setup_case('admin')
        self.assertIn('1-1-astra-F1', gate.history(gh, gh.pr)[2])
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call')):
            _, app, errors, state = run_pipeline(gh, app, event=event,
                provider=lambda _: (_ for _ in ()).throw(AssertionError('No review')))
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertEqual(state['reports']['astra']['review']['decision'], 'changes_requested')

    def test_revoked_admin_cannot_reuse_old_override_comment(self):
        gh, _, _ = self.setup_case('admin')
        self.assertTrue(gate.history(gh, gh.pr)[2])
        gh.permission = 'write'
        self.assertFalse(gate.history(gh, gh.pr)[2])

    def test_edited_admin_comments_never_authorize_overrides(self):
        changes = ({'updated_at': 'later'},
                   {'_lastEditedAt': 'now', '_editor': {'login': 'writer'}},
                   {'_lastEditedAt': 'later', '_editor': {'login': 'collaborator'}},
                   {'updated_at': None}, {'node_id': None})
        for change in changes:
            with self.subTest(change=change):
                gh, app, event = self.setup_case('admin')
                event['comment'].update(change)
                self.assertFalse(gate.history(gh, gh.pr)[2])
                with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call')):
                    _, app, errors, state = run_pipeline(gh, app, event=event,
                        provider=lambda _: (_ for _ in ()).throw(AssertionError('No review')))
                self.assertEqual(errors, [])
                self.assertIsNone(state)
                self.assertFalse(app.created)
                self.assertTrue(any('new, unedited admin comments' in p['body'] for p in gh.posts))

    def test_edit_metadata_must_match_the_exact_author_and_body(self):
        gh, _, event = self.setup_case('admin')
        original = gh.api('/graphql', 'POST', {'query': 'query($id:ID!)',
                                             'variables': {'id': event['comment']['node_id']}})
        import copy
        for change in ({'body': 'A different body'}, {'author': {'login': 'another-user'}},
                       {'id': 'another-node'}, {'__typename': 'PullRequest'}):
            with self.subTest(change=change):
                reply = copy.deepcopy(original)
                reply['data']['node'].update(change)
                with patch.object(gh, 'api', return_value=reply):
                    self.assertFalse(gate.history(gh, gh.pr)[2])
        for reply in ({'data': {'node': None}}, {'data': original['data'], 'errors': ['partial failure']},
                      {'data': {'node': {'id': event['comment']['node_id']}}}):
            with self.subTest(reply=reply), patch.object(gh, 'api', return_value=reply):
                self.assertFalse(gate.history(gh, gh.pr)[2])

    def test_a_forged_admin_comment_cannot_complete_a_genuine_override(self):
        gh, app, event = self.setup_case('admin')
        import json
        pair = json.loads(app.checks[5]['output']['text'])['reports']
        pair['astra']['review']['findings'].append({'id': 'F2', 'objection': 'A second real objection.'})
        app.prior(pair)
        forged = comment('/protocol-b override '+HEAD+' 1-1-astra-F2 Forged decision', 'collaborator')
        forged['_lastEditedAt'] = 'now'
        forged['_editor'] = {'login': 'writer'}
        gh.comments = [report_comment(e) for e in pair.values()]+[forged, event['comment']]
        self.assertEqual(set(gate.history(gh, gh.pr)[2]), {'1-1-astra-F1'})
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call')):
            _, app, errors, state = run_pipeline(gh, app, event=event,
                provider=lambda _: (_ for _ in ()).throw(AssertionError('No review')))
        self.assertTrue(errors)
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertIn('1-1-astra-F2', state['summary'])

    def test_ignored_override_reply_does_not_change_history_coverage(self):
        gh, app, event = self.setup_case('write')
        before = gate.history_coverage(gate.history(gh, gh.pr)[0])
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call')):
            _, _, errors, _ = run_pipeline(gh, app, event=event,
                provider=lambda _: (_ for _ in ()).throw(AssertionError('No review')))
        self.assertEqual(errors, [])
        for post in gh.posts:
            if post.get('body', '').startswith('This override was ignored.'):
                gh.comments.append(comment(post['body']))
        after = gate.history_coverage(gate.history(gh, gh.pr)[0])
        self.assertEqual(after, before)


if __name__ == '__main__':
    unittest.main()
