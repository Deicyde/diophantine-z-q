"""Serialized supplement chains and malformed-final peer retention."""
import copy
import json
import threading
import unittest
from unittest.mock import patch
from test_gate import gate, FakeGH, FakeApp, HEAD, report, comment, run_pipeline
from test_continuity import stored


class SupplementDelivery(unittest.TestCase):
    @staticmethod
    def accept(reviewer):
        reviewer.history_read = True
        reviewer.reads = [{'path': 'p.tex', 'revision': HEAD, 'start': 1, 'count': 1}]
        return report(report='Full original source review, including its argument.',
                      sources_read=['p.tex:1'])

    def original_round(self):
        gh = FakeGH()
        original = gh.call
        bodies = []
        def call(path, method='GET', data=None):
            if method == 'POST' and path.endswith('/comments') and data['body'].startswith(gate.MARKER):
                e = json.loads(data['body'].split('```json\n')[1].split('\n```')[0])
                if e['reviewer'] == 'astra':
                    bodies.append(data['body'])
                    raise RuntimeError('Only the original Astra report was not delivered')
            return original(path, method, data)
        gh.call = call
        _, app, _, state = run_pipeline(gh, provider=self.accept)
        self.assertEqual(state['reports']['fable']['report_publication']['status'], 'posted')
        self.assertEqual(app.final['conclusion'], 'failure')
        return json.loads(app.final['output']['text'])['reports'], bodies[0]

    def supplement_round(self, saved, discussion, arrived=None, interrupted=False):
        gh, app = FakeGH(), FakeApp()
        stored(app, gh, saved)
        gh.comments.append(comment(discussion, 'reader'))
        if arrived:
            gh.comments.append(comment(arrived))
        gh.permission = 'write'
        event = {'issue': {'number': 1}, 'comment': comment('/protocol-b review', 'collaborator'),
                 'sender': {'login': 'collaborator'}}
        seen = []
        def provider(reviewer):
            seen.append(reviewer.input)
            self.assertIn('retained_acceptance', reviewer.input)
            if interrupted:
                raise RuntimeError('Supplement interrupted')
            return self.accept(reviewer)
        _, app, _, state = run_pipeline(gh, app, event=event, provider=provider)
        self.assertEqual(len(seen), 1)
        return gh, app, state

    def test_delivered_supplement_does_not_replace_missing_original_report(self):
        saved, original = self.original_round()
        digest = saved['astra']['report_publication']['sha256']
        gh, app, state = self.supplement_round(saved, 'Please check this new observation.')
        self.assertEqual(state['reports']['astra']['report_publication']['status'], 'posted')
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertFalse(gh.merge_requests)
        second = json.loads(app.final['output']['text'])['reports']
        pending = second['astra']['retained_report_publications']
        self.assertEqual(pending[0]['report_publication']['sha256'], digest)
        # Serializing through another App record and supplement keeps the same debt.
        gh, app, state = self.supplement_round(second, 'Another genuinely new discussion item.')
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertEqual(state['reports']['astra']['retained_report_publications'][0]
                         ['report_publication']['sha256'], digest)
        self.assertFalse(gh.merge_requests)
        # Only the original report body, not the supplement, settles that debt.
        _, app, state = self.supplement_round(second, 'Another genuinely new discussion item.', arrived=original)
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertEqual(state['reports']['astra']['retained_report_publications'][0]
                         ['report_publication']['status'], 'posted')

    def test_interrupted_supplement_also_retains_original_publication(self):
        saved, _ = self.original_round()
        _, app, state = self.supplement_round(saved, 'New discussion', interrupted=True)
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertFalse(state['reports']['astra']['complete'])
        self.assertEqual(state['reports']['astra']['retained_report_publications'][0]
                         ['report_publication']['status'], 'failed')

    def test_malformed_final_containers_cannot_discard_valid_peer_rejection(self):
        for raw in (None, 42, True, 'not a list', {'F1': 'wrong container'},
                    [None, 42, {'id': 'G1', 'location': None, 'objection': 'Delivered gap'}]):
            with self.subTest(raw=raw):
                first_failed = threading.Event()
                def provider(reviewer):
                    if reviewer.family == 'astra':
                        reviewer.invalid_finish = {'findings': copy.deepcopy(raw)}
                        first_failed.set()
                        raise RuntimeError('Correction was interrupted')
                    self.assertTrue(first_failed.wait(3))
                    self.accept(reviewer)
                    return report(decision='changes_requested', findings=[
                        {'id': 'F1', 'objection': 'Valid peer counterexample'}])
                _, app, _, state = run_pipeline(provider=provider)
                saved = json.loads(app.final['output']['text'])['reports']
                self.assertTrue(saved['fable']['complete'])
                self.assertEqual(saved['fable']['review']['findings'][0]['id'], 'F1')
                self.assertFalse(saved['astra']['complete'])
                scopes = {item['id']: {} for item in state['scope_items']}
                with self.assertRaisesRegex(ValueError, '7-1-fable-F1'):
                    gate.overridden_decision(saved, scopes, HEAD)

    def test_failure_processing_exception_still_collects_peer(self):
        original = gate.record
        def record(name, value):
            if name == 'astra-failure.json':
                raise OSError('Failure artifact write unavailable')
            return original(name, value)
        def provider(reviewer):
            if reviewer.family == 'astra':
                raise RuntimeError('Review interrupted')
            self.accept(reviewer)
            return report(decision='changes_requested', findings=[{'id': 'F1', 'objection': 'Peer objection'}])
        with patch.object(gate, 'record', side_effect=record):
            _, app, _, state = run_pipeline(provider=provider)
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertTrue(state['reports']['fable']['complete'])
        self.assertEqual(state['reports']['fable']['review']['findings'][0]['id'], 'F1')
        self.assertIn('artifact write unavailable', state['reports']['astra']['post_review_error'])


if __name__ == '__main__':
    unittest.main()
