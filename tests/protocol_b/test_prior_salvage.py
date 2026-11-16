"""An interrupted prior disposition must survive the peer's resolution."""
import copy
import json
import unittest
from unittest.mock import patch
from test_gate import gate, FakeGH, FakeApp, HEAD, report, envelope, comment, report_comment, run_pipeline
from test_continuity import stored


class PriorSalvage(unittest.TestCase):
    ident = '1-1-astra-F1'

    def history(self, previously_resolved=False):
        gh, app = FakeGH(), FakeApp()
        old = 'c' * 40
        first = envelope(head=old, review=report(decision='changes_requested', findings=[
            {'id': 'F1', 'objection': 'The denominator can vanish.'}]))
        stored(app, gh, {'astra': first, 'fable': envelope('fable', head=old)}, head=old)
        gh.comments.append(report_comment(first))
        if previously_resolved:
            pair = {f: envelope(f, run='2', head=old, read_prerequisites_complete=True,
                review=report(prior_findings=[{'id': self.ident, 'resolution': 'resolved',
                    'reason': 'The old head contained the repair.'}])) for f in gate.MODELS}
            stored(app, gh, pair, ident=6, head=old)
        gh.permission = 'write'
        event = {'issue': {'number': 1}, 'comment': comment('/protocol-b review', 'collaborator'),
                 'sender': {'login': 'collaborator'}}
        return gh, app, event

    def test_actual_run_keeps_unresolved_disposition_when_peer_resolves_it(self):
        actual_run = gate.Review.run
        for previously_resolved in (False, True):
            for interruption in ('diagnostic', 'correction'):
                with self.subTest(previously_resolved=previously_resolved, interruption=interruption):
                    gh, app, event = self.history(previously_resolved)
                    original_record = gate.record
                    failed = []
                    def record(name, data):
                        if interruption == 'diagnostic' and name == 'fable-turns.json' and not failed:
                            failed.append(name)
                            raise OSError('One-shot diagnostic failure')
                        return original_record(name, data)
                    value = report(decision='changes_requested', prior_findings=[
                        {'id': self.ident, 'resolution': 'unresolved', 'reason': 'The repair is wrong on this head.'}])
                    if interruption == 'correction':
                        value['report'] = 'Invalid short prose'
                    response = ([{'type': 'tool_use', 'id': 'final', 'name': 'finish_review', 'input': value}],
                                gate.MODELS['fable'], {}, 'response-1', 'end_turn')
                    def provider(reviewer):
                        self.assertIn(self.ident, reviewer.prior)
                        reviewer.history_read = True
                        reviewer.reads = [{'path': 'p.tex', 'revision': HEAD, 'start': 1, 'count': 1}]
                        if reviewer.family == 'fable':
                            return actual_run(reviewer)
                        return report(prior_findings=[{'id': self.ident, 'resolution': 'resolved',
                                                       'reason': 'Peer believes the repaired source is sufficient.'}])
                    with patch.object(gate, 'record', side_effect=record), \
                         patch.object(gate, 'model_turn', side_effect=[response, RuntimeError('Correction interrupted')]):
                        _, app, _, state = run_pipeline(gh, app, event=event, provider=provider)
                    saved = json.loads(app.final['output']['text'])['reports']
                    self.assertEqual(saved['astra']['review']['prior_findings'][0]['resolution'], 'resolved')
                    self.assertFalse(saved['fable']['complete'])
                    prior = saved['fable']['review']['prior_findings']
                    self.assertEqual(prior[0]['id'], self.ident)
                    self.assertEqual(prior[0]['resolution'], 'unresolved')
                    self.assertIn('Unvalidated delivered disposition', prior[0]['reason'])
                    scopes = {item['id']: {} for item in state['scope_items']}
                    with self.assertRaisesRegex(ValueError, self.ident):
                        gate.overridden_decision(saved, scopes, HEAD)
                    self.assertEqual(app.final['conclusion'], 'failure')

    def test_salvage_is_bounded_to_known_ids_and_safe_json_containers(self):
        for raw in (None, 42, {}, 'bad', [None, {'id': []}, {'id': 'unknown', 'resolution': 'unresolved'},
                   {'id': self.ident, 'resolution': 'resolved'},
                   {'id': self.ident, 'resolution': None, 'reason': {'missing': 'validation'}}]):
            with self.subTest(raw=raw):
                gh, app, event = self.history()
                def provider(reviewer):
                    if reviewer.family == 'fable':
                        reviewer.invalid_finish = {'findings': [], 'prior_findings': copy.deepcopy(raw)}
                        raise RuntimeError('Interrupted invalid final')
                    reviewer.history_read = True
                    reviewer.reads = [{'path': 'p.tex', 'revision': HEAD, 'start': 1, 'count': 1}]
                    return report(prior_findings=[{'id': self.ident, 'resolution': 'resolved', 'reason': 'Peer repair.'}])
                _, app, _, state = run_pipeline(gh, app, event=event, provider=provider)
                self.assertTrue(state['reports']['astra']['complete'])
                prior = state['reports']['fable']['review']['prior_findings']
                self.assertTrue(all(p['id'] == self.ident and p['resolution'] == 'unresolved' for p in prior))
                if isinstance(raw, list):
                    self.assertEqual(len(prior), 1)
                    self.assertIn('Unvalidated delivered disposition', prior[0]['reason'])


if __name__ == '__main__':
    unittest.main()
