"""Actual Review.run must preserve final calls before diagnostic failures."""
import json
import unittest
from unittest.mock import patch
from test_gate import gate, HEAD, report, run_pipeline


class FinalCapture(unittest.TestCase):
    def test_delivered_objection_survives_diagnostic_write_failure(self):
        actual_run = gate.Review.run
        for family, diagnostic in [('astra', 'astra-turns.json'), ('fable', 'fable-turns.json'),
                                   ('fable', 'fable-web-results.json'),
                                   ('astra', 'astra-delivered-final.json'),
                                   ('fable', 'fable-delivered-final.json')]:
            with self.subTest(family=family, diagnostic=diagnostic):
                value = report(decision='changes_requested', findings=[
                    {'id': 'F1', 'objection': 'A final delivered counterexample, before diagnostics.'}])
                if family == 'astra':
                    output = [{'type': 'function_call', 'name': 'finish_review', 'call_id': 'final',
                               'arguments': json.dumps(value)}]
                else:
                    output = [{'type': 'tool_use', 'name': 'finish_review', 'id': 'final', 'input': value}]
                original_record = gate.record
                failed = []
                def record(name, data):
                    if name == diagnostic and not failed:
                        failed.append(name)
                        raise OSError('One-shot diagnostic write failure')
                    return original_record(name, data)
                def provider(reviewer):
                    reviewer.history_read = True
                    reviewer.reads = [{'path': 'p.tex', 'revision': HEAD, 'start': 1, 'count': 1}]
                    return actual_run(reviewer) if reviewer.family == family else report()
                response = (output, gate.MODELS[family], {}, 'response-1', 'end_turn')
                with patch.object(gate, 'record', side_effect=record), \
                     patch.object(gate, 'model_turn', return_value=response) as model:
                    _, app, _, state = run_pipeline(provider=provider)
                self.assertEqual(failed, [diagnostic])
                self.assertEqual(model.call_count, 1)
                saved = json.loads(app.final['output']['text'])['reports']
                self.assertFalse(saved[family]['complete'])
                self.assertEqual(saved[family]['review']['findings'][0]['id'], 'F1')
                peer = 'fable' if family == 'astra' else 'astra'
                self.assertTrue(saved[peer]['complete'])
                scopes = {item['id']: {} for item in state['scope_items']}
                with self.assertRaisesRegex(ValueError, '7-1-'+family+'-F1'):
                    gate.overridden_decision(saved, scopes, HEAD)

    def test_model_identity_is_checked_before_any_response_diagnostic(self):
        actual_run = gate.Review.run
        original_record = gate.record
        response_diagnostics = []
        def record(name, data):
            if name in {'fable-web-results.json', 'fable-turns.json', 'fable-delivered-final.json'}:
                response_diagnostics.append(name)
                raise OSError('Diagnostic cannot mask identity error')
            return original_record(name, data)
        def provider(reviewer):
            return actual_run(reviewer) if reviewer.family == 'fable' else report()
        response = ([{'type': 'tool_use', 'name': 'finish_review', 'id': 'final', 'input': report()}],
                    'unapproved-model', {}, 'response-1', 'end_turn')
        with patch.object(gate, 'record', side_effect=record), \
             patch.object(gate, 'model_turn', return_value=response):
            _, app, _, state = run_pipeline(provider=provider)
        self.assertFalse(response_diagnostics)
        self.assertTrue(state['reports']['fable']['identity_error'])
        self.assertEqual(app.final['conclusion'], 'failure')
        scopes = {item['id']: {} for item in state['scope_items']}
        with self.assertRaises(ValueError):
            gate.overridden_decision(state['reports'], scopes, HEAD)


if __name__ == '__main__':
    unittest.main()
