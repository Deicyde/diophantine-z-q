"""Unsuccessful final submissions can add obligations, but cannot close them."""
import copy
import json
import unittest
from unittest.mock import patch
from test_gate import gate, HEAD, report, run_pipeline
import test_prior_salvage as prior_fixtures


def response(family, values, turn):
    calls = []
    for i, value in enumerate(values):
        if family == 'astra':
            calls.append({'type': 'function_call', 'name': 'finish_review',
                          'call_id': f'{turn}-{i}', 'arguments': json.dumps(value)})
        else:
            calls.append({'type': 'tool_use', 'name': 'finish_review',
                          'id': f'{turn}-{i}', 'input': value})
    return calls, gate.MODELS[family], {}, turn, 'end_turn'


class DeliveredClosure(unittest.TestCase):
    def fixture(self, family, first, later, *, old=False, diagnostic=None):
        actual_run, original_record = gate.Review.run, gate.record
        gh, app, event = prior_fixtures.PriorSalvage().history(True) if old else (None, None, None)
        failed, workers = [], {}
        def record(name, value):
            if name == diagnostic and not failed:
                failed.append(name)
                raise OSError('One-shot diagnostic failure')
            return original_record(name, value)
        def provider(reviewer):
            workers[reviewer.family] = reviewer
            reviewer.history_read = True
            reviewer.reads = [{'path': 'p.tex', 'revision': HEAD, 'start': 1, 'count': 1}]
            if reviewer.family == family:
                return actual_run(reviewer)
            return report(prior_findings=[{'id': ident, 'resolution': 'resolved',
                'reason': 'The peer checked the repaired source.'} for ident in reviewer.prior])
        with patch.object(gate, 'record', side_effect=record), \
             patch.object(gate, 'model_turn', side_effect=[first, *later]) as model:
            result = run_pipeline(gh, app, event=event, provider=provider)
        return result, workers, model.call_count, failed

    def test_two_invalid_finals_and_interruption_keep_all_objections(self):
        for family in gate.MODELS:
            for prior in (False, True):
                for replacement in ({}, {'findings': None}, {'prior_findings': []}):
                    with self.subTest(family=family, prior=prior, replacement=replacement):
                        value = report(report='Too short', decision='changes_requested')
                        ident = prior_fixtures.PriorSalvage.ident if prior else '7-1-'+family+'-F1'
                        if prior:
                            value['prior_findings'] = [{'id': ident, 'resolution': 'unresolved',
                                'reason': 'An actual counterexample to the earlier repair.'}]
                        else:
                            value['findings'] = [{'id': 'F1', 'objection': 'An actual new counterexample.'}]
                        (gh, app, _, state), workers, count, _ = self.fixture(family,
                            response(family, [value], 'one'),
                            [response(family, [replacement], 'two'), RuntimeError('Correction interrupted')], old=prior)
                        self.assertEqual(count, 3)
                        self.assertEqual(app.final['conclusion'], 'failure')
                        self.assertFalse(gh.merge_requests)
                        saved = json.loads(app.final['output']['text'])['reports']
                        self.assertFalse(saved[family]['complete'])
                        scopes = {i['id']: {} for i in state['scope_items']}
                        with self.assertRaisesRegex(ValueError, ident):
                            gate.overridden_decision(saved, scopes, HEAD)
                        if not prior:
                            peer = 'fable' if family == 'astra' else 'astra'
                            self.assertNotIn(ident, workers[peer].prior)

    def test_all_concurrent_finals_captured_before_diagnostics(self):
        for family in gate.MODELS:
            with self.subTest(family=family):
                values = [report(decision='changes_requested', findings=[
                    {'id': ident, 'objection': 'Counterexample '+ident}]) for ident in ('F1', 'F2')]
                (_, app, _, state), _, count, failed = self.fixture(family,
                    response(family, values, 'one'), [], diagnostic=family+'-delivered-finals.json')
                self.assertEqual(count, 1)
                self.assertTrue(failed)
                saved = json.loads(app.final['output']['text'])['reports']
                self.assertEqual({f['id'] for f in saved[family]['review']['findings']}, {'F1', 'F2'})
                scopes = {i['id']: {} for i in state['scope_items']}
                with self.assertRaisesRegex(ValueError, 'F1.*F2'):
                    gate.overridden_decision(saved, scopes, HEAD)

    def test_corrected_acceptance_must_explicitly_resolve_earlier_delivery(self):
        for family in gate.MODELS:
            for closure in ('omit', 'resolve', 'retain'):
                with self.subTest(family=family, closure=closure):
                    invalid = report(report='Short', decision='changes_requested', findings=[
                        {'id': 'F1', 'location': 'p.tex:1', 'objection': 'The denominator may vanish.'}])
                    corrected = report()
                    ident = '7-1-'+family+'-F1'
                    if closure == 'resolve':
                        corrected['prior_findings'] = [{'id': ident, 'resolution': 'resolved',
                            'reason': 'Read p.tex:1; the premise states the denominator is nonzero.'}]
                    elif closure == 'retain':
                        corrected = report(decision='changes_requested', findings=copy.deepcopy(invalid['findings']))
                    later = [response(family, [corrected], 'two')]
                    if closure == 'omit':
                        later.append(RuntimeError('No correction available'))
                    (_, app, _, state), workers, count, _ = self.fixture(family,
                        response(family, [invalid], 'one'), later)
                    self.assertEqual(count, 3 if closure == 'omit' else 2)
                    self.assertEqual(app.final['conclusion'], 'success' if closure == 'resolve' else 'failure')
                    self.assertEqual(state['reports'][family]['complete'], closure != 'omit')
                    if closure != 'omit':
                        self.assertEqual(workers[family].pending_payloads(), [])


if __name__ == '__main__':
    unittest.main()
