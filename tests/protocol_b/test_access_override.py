import copy
import json
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

    def test_all_qualified_access_requires_ordinary_review(self):
        pair = test_continuity.AccessLimitations().pair()
        with self.assertRaisesRegex(ValueError, 'No deadlock needs overriding'):
            gate.overridden_decision(pair, {}, HEAD)

    def test_missing_peer_evidence_still_requires_explicit_override(self):
        pair = self.pair()
        pair['fable']['review']['source_checks'].clear()
        with self.assertRaisesRegex(ValueError, '1-1-astra-F1'):
            gate.overridden_decision(pair, {'1-1-astra-F2': {}}, HEAD)

    def test_mismatched_peer_passage_still_requires_explicit_override(self):
        pair = self.pair()
        pair['fable']['review']['source_checks'][0]['source_id'] += ' different passage'
        self.assertEqual(gate.qualified_access_findings(pair), [])
        with self.assertRaisesRegex(ValueError, '1-1-astra-F1'):
            gate.overridden_decision(pair, {'1-1-astra-F2': {}}, HEAD)

    def test_reciprocal_access_limitations_each_need_the_other_passage(self):
        pair = test_continuity.AccessLimitations().pair()
        source = 'Second published proposition'
        pair['astra']['review']['source_checks'].append({
            'source_id': source, 'location': 'p. 4', 'outcome': 'verified',
            'detail': 'Read the statement and its application without objection.'})
        pair['fable']['review'].update(decision='changes_requested', findings=[
            {'id': 'F2', 'location': 'p.tex:8', 'objection': 'Could not open the second source.'}],
            access_limitations=[{'finding_id': 'F2', 'source_ids': [source],
                                 'detail': 'Only source access is missing.'}])
        self.assertEqual({item['finding'] for item in gate.qualified_access_findings(pair)},
                         {'1-1-astra-F1', '1-1-fable-F2'})
        pair['astra']['review']['source_checks'].pop()
        self.assertEqual([item['finding'] for item in gate.qualified_access_findings(pair)],
                         ['1-1-astra-F1'])

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

    def test_uncovered_discussion_and_ineffective_override_never_grant_success(self):
        for command_text in (
                '/protocol-b override malformed',
                '/protocol-b override '+('f' * 40)+' 1-1-astra-F1 Stale head',
                '/protocol-b override '+HEAD+' 1-1-astra-UNKNOWN Unknown finding'):
            with self.subTest(command=command_text):
                gh, app = FakeGH(), FakeApp()
                gh.permission = 'admin'
                pair = test_continuity.AccessLimitations().pair()
                app.prior(pair)
                command = comment(command_text, 'collaborator')
                gh.comments = [report_comment(e) for e in pair.values()]
                gh.comments += [comment('A new substantive objection was not reviewed.', 'reader'), command]
                event = {'issue': {'number': 1}, 'comment': command,
                         'sender': {'login': 'collaborator'}}
                with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call')):
                    _, app, errors, state = run_pipeline(gh, app, event=event,
                        provider=lambda _: (_ for _ in ()).throw(AssertionError('No review call')))
                self.assertTrue(errors)
                self.assertEqual(app.final['conclusion'], 'failure')
                self.assertIn('No deadlock needs overriding', state['summary'])
                self.assertFalse(gh.merge_requests)
                self.assertIsNone(gh.graphql)
                self.assertEqual(state['reports'], pair)

    def test_failed_partial_override_preserves_limitations_in_app_and_summary(self):
        gh, app = FakeGH(), FakeApp()
        gh.permission = 'admin'
        pair = self.pair()
        pair['astra']['review']['findings'].append({
            'id': 'F3', 'location': 'p.tex:12', 'objection': 'Another substantive objection.'})
        app.prior(pair)
        command = comment('/protocol-b override '+HEAD+' 1-1-astra-F2 Owner decision', 'collaborator')
        gh.comments = [report_comment(e) for e in pair.values()]+[command]
        event = {'issue': {'number': 1}, 'comment': command, 'sender': {'login': 'collaborator'}}
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call')):
            _, app, errors, state = run_pipeline(gh, app, event=event,
                provider=lambda _: (_ for _ in ()).throw(AssertionError('No review call')))
        self.assertTrue(errors)
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertIn('Uncovered findings: 1-1-astra-F3', state['summary'])
        payload = json.loads(app.final['output']['text'])
        self.assertEqual([item['finding'] for item in payload['source_access_limitations']],
                         ['1-1-astra-F1'])
        summary = gate.round_summary_body(state, 'x/y', 'https://example.test/check')
        self.assertIn('`1-1-astra-F1`: Source access: fable verified', summary)
        self.assertIn('`1-1-astra-F3`: p.tex:12: Another substantive objection.', summary)
        self.assertFalse(gh.merge_requests)
        self.assertEqual(state['reports'], pair)


if __name__ == '__main__':
    unittest.main()
