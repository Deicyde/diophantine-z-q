import copy
import json
import os
import unittest
from unittest.mock import patch

from test_gate import gate, FakeGH, FakeApp, HEAD, BASE, envelope, report, comment, report_comment, run_pipeline


class ScopeOverride(unittest.TestCase):
    def pair(self, **changes):
        return {'astra': envelope(review=report(decision='changes_requested', scope_complete=False,
                        not_reviewed=['The application of Theorem 3 on p. 14 was not reviewed.']), **changes),
                'fable': envelope('fable')}

    def test_scope_is_a_distinct_stable_item_and_needs_its_own_override(self):
        pair = self.pair()
        original = copy.deepcopy(pair)
        item = gate.review_scope_item(pair['astra'])
        self.assertEqual(item['id'], 'scope-1-1-astra')
        self.assertEqual(item['kind'], 'review_scope')
        self.assertIn('Theorem 3', item['not_reviewed'][0])
        with self.assertRaisesRegex(ValueError, 'Uncovered findings: scope-1-1-astra'):
            gate.overridden_decision(pair, {}, HEAD)
        self.assertEqual(gate.overridden_decision(pair, {item['id']: {'reason': 'Owner decision'}}, HEAD),
                         {item['id']: {'reason': 'Owner decision'}})
        self.assertFalse(gate.combined_decision(pair)[0])
        self.assertEqual(pair, original)

    def test_missing_reads_and_interruption_are_overridable_but_never_auto_accept(self):
        for changes in ({'read_prerequisites_complete': False}, {'complete': False}, {'finished_early': True}):
            with self.subTest(changes=changes):
                pair = self.pair(**changes)
                self.assertFalse(gate.combined_decision(pair)[0])
                self.assertIn('scope-1-1-astra', gate.overridden_decision(pair, {'scope-1-1-astra': {}}, HEAD))

    def test_rejection_without_findings_or_notes_still_blocks_and_is_overridable(self):
        pair = self.pair()
        pair['astra']['review'] = report(decision='changes_requested')
        self.assertFalse(gate.combined_decision(pair)[0])
        item = gate.review_scope_item(pair['astra'])
        self.assertIn('without an itemized blocking finding', item['objection'])
        self.assertIn(item['id'], gate.overridden_decision(pair, {item['id']: {}}, HEAD))

    def test_substantive_finding_requires_override_in_addition_to_scope(self):
        pair = self.pair()
        pair['astra']['review']['findings'] = [{'id': 'F1', 'severity': 'blocking', 'objection': 'A counterexample'}]
        with self.assertRaisesRegex(ValueError, 'Uncovered findings: 1-1-astra-F1'):
            gate.overridden_decision(pair, {'scope-1-1-astra': {}}, HEAD)
        self.assertEqual(set(gate.overridden_decision(pair, {'scope-1-1-astra': {}, '1-1-astra-F1': {}}, HEAD)),
                         {'scope-1-1-astra', '1-1-astra-F1'})

    def test_stale_and_wrong_models_are_not_coverage_overrides(self):
        for changes in ({'head': BASE}, {'model': 'different-model'}, {'identity_error': True}):
            with self.subTest(changes=changes), self.assertRaisesRegex(ValueError, 'stale or wrong-model'):
                gate.overridden_decision(self.pair(**changes), {'scope-1-1-astra': {}}, HEAD)

    def test_not_reviewed_list_is_required_for_explicit_incomplete_scope(self):
        with self.assertRaisesRegex(ValueError, 'must identify what was not reviewed'):
            gate.validate_review(report(decision='changes_requested', scope_complete=False), set(), {})
        with self.assertRaisesRegex(ValueError, 'cannot be called complete'):
            gate.validate_review(report(not_reviewed=['Unread lemma']), set(), {})

    def test_app_payload_keeps_scope_after_long_report_text_is_removed(self):
        pair = self.pair()
        original = gate.review_scope_item(pair['astra'])
        payload = json.loads(gate.decision_text({'head': HEAD}, pair, []))
        self.assertNotIn('report', payload['reports']['astra']['review'])
        self.assertEqual(gate.review_scope_item(payload['reports']['astra']), original)

    def test_large_scope_remains_explicitly_overridable_with_original_binding(self):
        pair = self.pair()
        pair['astra']['review']['not_reviewed'] = ['Unread argument '+str(i)+' '+('x'*1200) for i in range(100)]
        original = copy.deepcopy(pair)
        scope = gate.review_scope_item(pair['astra'])
        self.assertEqual(scope['coverage_omitted']['items'], 100)
        payload = json.loads(gate.decision_text({'head': HEAD}, pair, []))
        self.assertLess(len(json.dumps(payload).encode()), 10_000)
        saved = payload['reports']
        self.assertEqual(gate.review_scope_item(saved['astra']), scope)
        self.assertEqual(gate.overridden_decision(saved, {scope['id']: {}}, HEAD), {scope['id']: {}})
        self.assertFalse(gate.combined_decision(saved)[0])
        self.assertEqual(pair, original)

    def test_scope_comments_require_current_admin_at_both_checks(self):
        for permission in ('read', 'write', 'maintain', 'admin'):
            with self.subTest(permission=permission):
                gh, app = FakeGH(), FakeApp()
                gh.permission = permission
                pair = self.pair()
                app.prior(pair)
                command = comment('/protocol-b override '+HEAD+' scope-1-1-astra Accept explicitly incomplete coverage', 'collaborator')
                gh.comments = [report_comment(e) for e in pair.values()]+[command]
                overrides = gate.history(gh, gh.pr)[2]
                self.assertEqual(bool(overrides), permission == 'admin')
                event = {'issue': {'number': 1}, 'comment': command, 'sender': {'login': 'collaborator'}}
                with patch.object(gate, 'model_turn', side_effect=AssertionError('No model allowed')):
                    _, app, errors, state = run_pipeline(gh, app, event=event,
                        provider=lambda _: (_ for _ in ()).throw(AssertionError('No review allowed')))
                self.assertEqual(errors, [])
                if permission == 'admin':
                    self.assertEqual(app.final['conclusion'], 'success')
                    self.assertFalse(state['reports']['astra']['review']['scope_complete'])
                    self.assertEqual(state['scope_overrides'][0]['id'], 'scope-1-1-astra')
                    self.assertIn('Accepted by admin with incomplete reviewer scope', state['summary'])
                else:
                    self.assertEqual(app.created, [])
                    if permission in ('write', 'maintain'):
                        self.assertTrue(any('override was ignored' in p['body'] for p in gh.posts))

    def test_scope_only_runtime_record_does_not_claim_a_model_ran(self):
        state = {'head': HEAD, 'policy_ref': BASE, 'reports': {}, 'summary': 'The review did not start.'}
        with patch.dict(os.environ, {'GITHUB_RUN_ID': '7', 'GITHUB_RUN_ATTEMPT': '1'}):
            gate.ensure_scope_records(state)
        self.assertEqual(len(state['scope_items']), 2)
        for value in state['reports'].values():
            self.assertFalse(value['complete'])
            self.assertTrue(value['runtime_scope_record'])
            self.assertIsNone(value['reported_model'])
            self.assertEqual(value['review']['decision'], 'not_reviewed')
        allowed = {i['id']: {'reason': 'Explicit admin decision'} for i in state['scope_items']}
        self.assertEqual(gate.overridden_decision(state['reports'], allowed, HEAD), allowed)

    def test_scope_overrides_show_coverage_not_model_acceptance(self):
        pair = self.pair()
        state = {'number': 1, 'head': HEAD, 'check': 20, 'conclusion': 'success', 'reports': pair,
                 'overrides': {'scope-1-1-astra': {'reason': 'Explicit admin choice'}}}
        text = gate.round_summary_body(state, 'x/y', 'check')
        self.assertIn('Astra: did not complete', text)
        self.assertIn('Admin accepted incomplete review scope', text)
        self.assertIn('Theorem 3', text)
        self.assertIn('"blocking_count": 0', text)

    def test_next_step_names_the_current_scope_id_and_admin(self):
        state = {'number': 1, 'head': HEAD, 'check': 20, 'conclusion': 'failure',
                 'reports': self.pair(run='27'), 'overrides': {}}
        text = gate.round_summary_body(state, 'x/y', 'check').split('### Next step', 1)[1]
        self.assertIn('request an admin decision', text)
        self.assertIn('`scope-27-1-astra`', text)
        self.assertNotIn('`scope-1-1-astra`', text)

    def test_later_skipped_run_does_not_erase_previous_substantive_rejection(self):
        previous = self.pair()
        previous['astra']['review']['findings'] = [{'id': 'F1', 'objection': 'A counterexample.'}]
        state = {'head': HEAD, 'policy_ref': BASE, 'reports': {}, 'summary': 'A later run did not start.'}
        with patch.dict(os.environ, {'GITHUB_RUN_ID': '7', 'GITHUB_RUN_ATTEMPT': '1'}):
            gate.ensure_scope_records(state, previous)
        self.assertEqual(state['reports']['astra']['review'], previous['astra']['review'])
        with self.assertRaisesRegex(ValueError, '1-1-astra-F1'):
            gate.overridden_decision(state['reports'], {'scope-1-1-astra': {}}, HEAD)

    def test_admin_can_override_a_recorded_run_that_never_reached_the_models(self):
        gh = FakeGH()
        gh.author_permission = 'read'
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call')):
            _, app, _, state = run_pipeline(gh)
        self.assertEqual(len(state['scope_items']), 2)
        saved = json.loads(app.final['output']['text'])['reports']
        next_gh, next_app = FakeGH(), FakeApp()
        next_gh.permission = 'admin'
        next_app.prior(saved)
        next_gh.comments = [comment('/protocol-b override '+HEAD+' '+item['id']+' Explicitly accept the absent review',
                                    'collaborator') for item in state['scope_items']]
        event = {'issue': {'number': 1}, 'comment': next_gh.comments[-1], 'sender': {'login': 'collaborator'}}
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call')):
            _, accepted_app, errors, accepted = run_pipeline(next_gh, next_app, event=event,
                provider=lambda _: (_ for _ in ()).throw(AssertionError('No review allowed')))
        self.assertEqual(errors, [])
        self.assertEqual(accepted_app.final['conclusion'], 'success')
        self.assertEqual(len(accepted['scope_overrides']), 2)
        self.assertTrue(all(not r['complete'] for r in accepted['reports'].values()))

    def test_interrupted_replacement_cannot_erase_an_earlier_app_objection(self):
        previous = self.pair()
        previous['astra']['review']['findings'] = [{'id': 'F1', 'objection': 'A counterexample.'}]
        replacement = self.pair(complete=False, run='2')
        state = {'head': HEAD, 'policy_ref': BASE, 'reports': replacement}
        gate.ensure_scope_records(state, previous)
        with self.assertRaisesRegex(ValueError, '1-1-astra-F1'):
            gate.overridden_decision(state['reports'], {'scope-2-1-astra': {}}, HEAD)
        self.assertEqual(set(gate.overridden_decision(state['reports'],
                         {'scope-2-1-astra': {}, '1-1-astra-F1': {}}, HEAD)),
                         {'scope-2-1-astra', '1-1-astra-F1'})


if __name__ == '__main__':
    unittest.main()
