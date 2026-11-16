import copy
import unittest
from unittest.mock import patch

import test_continuity
from test_gate import gate, FakeGH, FakeApp, HEAD, comment, report_comment, run_pipeline


class AccessOverride(unittest.TestCase):
    def pair(self):
        pair = test_continuity.AccessLimitations().pair()
        pair['astra']['review']['findings'].append({
            'id': 'F2', 'location': 'p.tex:9', 'objection': 'An independent substantive finding.'})
        return pair

    def test_mixed_rejection_retains_qualified_access_record(self):
        pair = self.pair()
        original = copy.deepcopy(pair)
        accepted, limits = gate.combined_decision(pair)
        self.assertFalse(accepted)
        self.assertEqual([item['finding'] for item in limits], ['1-1-astra-F1'])
        self.assertEqual(pair, original)

    def test_only_substantive_finding_requires_override(self):
        pair = self.pair()
        self.assertEqual(gate.overridden_decision(pair, {'1-1-astra-F2': {'reason': 'Owner decision'}}, HEAD),
                         {'1-1-astra-F2': {'reason': 'Owner decision'}})
        with self.assertRaisesRegex(ValueError, 'Uncovered findings: 1-1-astra-F2$'):
            gate.overridden_decision(pair, {}, HEAD)

    def test_no_override_needed_when_all_findings_are_qualified_access(self):
        pair = test_continuity.AccessLimitations().pair()
        self.assertEqual(gate.overridden_decision(pair, {}, HEAD), {})

    def test_missing_peer_evidence_still_requires_explicit_override(self):
        pair = self.pair()
        pair['fable']['review']['source_checks'].clear()
        with self.assertRaisesRegex(ValueError, '1-1-astra-F1'):
            gate.overridden_decision(pair, {'1-1-astra-F2': {}}, HEAD)

    def test_unqualified_occurrence_of_same_id_is_not_dismissed(self):
        pair = self.pair()
        pair['fable']['review'].update(decision='changes_requested', prior_findings=[{
            'id': '1-1-astra-F1', 'resolution': 'unresolved', 'reason': 'An actual hypothesis fails.'}])
        self.assertEqual(gate.qualified_access_findings(pair), [])
        with self.assertRaisesRegex(ValueError, '1-1-astra-F1'):
            gate.overridden_decision(pair, {'1-1-astra-F2': {}}, HEAD)

    def test_missing_override_for_previously_overridden_occurrence_is_not_hidden(self):
        pair = self.pair()
        pair['fable']['review']['prior_findings'] = [{
            'id': '1-1-astra-F1', 'resolution': 'overridden', 'reason': 'An earlier owner decision.'}]
        with self.assertRaisesRegex(ValueError, '1-1-astra-F1'):
            gate.overridden_decision(pair, {'1-1-astra-F2': {}}, HEAD)

    def test_override_pipeline_calls_no_model_and_records_access_relief(self):
        gh, app = FakeGH(), FakeApp()
        pair = self.pair()
        app.prior(pair)
        gh.permission = 'write'
        command = comment('/protocol-b override '+HEAD+' 1-1-astra-F2 Accepted by owner', 'collaborator')
        gh.comments = [report_comment(e) for e in pair.values()]+[command]
        event = {'issue': {'number': 1}, 'comment': command, 'sender': {'login': 'collaborator'}}
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call')):
            _, app, errors, state = run_pipeline(gh, app, event=event,
                provider=lambda _: (_ for _ in ()).throw(AssertionError('No review call')))
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertEqual(set(state['overrides']), {'1-1-astra-F2'})
        self.assertEqual([item['finding'] for item in state['source_access_limitations']], ['1-1-astra-F1'])
        self.assertEqual(state['reports']['astra']['review']['decision'], 'changes_requested')


if __name__ == '__main__':
    unittest.main()
