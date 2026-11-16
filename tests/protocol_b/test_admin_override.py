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


if __name__ == '__main__':
    unittest.main()
