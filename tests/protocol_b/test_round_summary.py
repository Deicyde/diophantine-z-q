import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from test_gate import gate, FakeGH, HEAD, envelope, report, comment, run_pipeline


class RoundSummary(unittest.TestCase):
    def state(self, **updates):
        return {'number': 1, 'head': HEAD, 'check': 20, 'conclusion': 'success',
                'reports': {'astra': envelope(), 'fable': envelope('fable')}, **updates}

    def test_acceptance_is_readable_before_json(self):
        text = gate.round_summary_body(self.state(), 'x/y', 'https://example.test/check')
        self.assertLess(text.index('Review requirement met'), text.index('```json'))
        self.assertIn('Astra: accepted; Fable: accepted', text)
        self.assertIn('No review changes are required', text)

    def test_blocker_and_nonblocking_access_are_separate(self):
        reports = {'astra': envelope(review=report(decision='changes_requested', findings=[
            {'id': 'F1', 'location': 'p:7', 'objection': 'False inequality'},
            {'id': 'F2', 'location': 'p:9', 'objection': 'Source unavailable'}])),
            'fable': envelope('fable')}
        limits = [{'finding': '1-1-astra-F2', 'reviewer_who_checked': 'fable', 'reviewer_unable_to_open': 'astra'}]
        state = self.state(conclusion='failure', reports=reports, source_access_limitations=limits)
        before = copy.deepcopy(state)
        text = gate.round_summary_body(state, 'x/y', 'https://example.test/check')
        self.assertIn('`1-1-astra-F1`: p:7: False inequality', text)
        self.assertIn('`1-1-astra-F2`: Source access: fable verified', text)
        self.assertIn('"blocking_count": 1', text)
        self.assertIn('"nonblocking_count": 1', text)
        self.assertEqual(state, before)

    def test_override_does_not_relabel_reviewers_as_accepting(self):
        reports = {'astra': envelope(review=report(decision='changes_requested', findings=[{'id': 'F1', 'objection': 'Gap'}]))}
        text = gate.round_summary_body(self.state(reports=reports, overrides={'1-1-astra-F1': {}}), 'x/y', 'check')
        self.assertIn('Astra: requested changes', text)
        self.assertIn('recorded maintainer override', text)
        self.assertIn('not outside reviewed', text)
        self.assertIn('"blocking_count": 0', text)

    def test_peer_objection_wins_over_other_reviewers_access_relief_in_both_orders(self):
        ident = '1-1-astra-F1'
        reports = {
            'astra': envelope(review=report(decision='changes_requested', findings=[
                {'id': 'F1', 'location': 'p:7', 'objection': 'Source unavailable'}])),
            'fable': envelope('fable', review=report(decision='changes_requested', prior_findings=[
                {'id': ident, 'resolution': 'unresolved', 'reason': 'The source hypothesis fails.'}]))}
        limits = [{'finding': ident, 'reviewer_who_checked': 'fable', 'reviewer_unable_to_open': 'astra'}]
        for ordered in (reports, dict(reversed(list(reports.items())))):
            with self.subTest(order=list(ordered)):
                state = self.state(conclusion='failure', reports=ordered, source_access_limitations=limits)
                original = copy.deepcopy(state)
                text = gate.round_summary_body(state, 'x/y', 'check')
                self.assertIn('`'+ident+'`: The source hypothesis fails.', text)
                self.assertIn('"blocking_count": 1', text)
                self.assertIn('"nonblocking_count": 0', text)
                self.assertNotIn('this alone is not a mathematical error', text)
                self.assertEqual(state, original)

    def test_two_valid_reviewer_specific_limitations_keep_both_descriptions(self):
        ident = 'earlier-access-finding'
        reports = {}
        for family, missing, verified in [('astra', 'P', 'Q'), ('fable', 'Q', 'P')]:
            value = report(decision='changes_requested', prior_findings=[{
                'id': ident, 'resolution': 'unresolved', 'reason': 'I could not obtain passage '+missing}],
                source_checks=[{'source_id': missing, 'location': 'Theorem '+missing,
                                'outcome': 'unavailable', 'detail': 'This exact published passage could not be opened.'},
                               {'source_id': verified, 'location': 'Theorem '+verified,
                                'outcome': 'verified', 'detail': 'I read this exact passage and checked its application.'}],
                access_limitations=[{'finding_id': ident, 'source_ids': [missing],
                                     'detail': 'Only access to the named published passage remains unavailable.'}])
            gate.validate_review(value, {ident}, {})
            reports[family] = envelope(family, review=value)
        rendered = []
        for ordered in (reports, dict(reversed(list(reports.items())))):
            accepted, limits = gate.combined_decision(ordered, {ident: {}})
            self.assertTrue(accepted)
            self.assertEqual(len(limits), 2)
            state = self.state(reports=ordered, source_access_limitations=limits)
            original = copy.deepcopy(state)
            text = gate.round_summary_body(state, 'x/y', 'check')
            self.assertIn('"blocking_count": 0', text)
            self.assertIn('"nonblocking_count": 1', text)
            self.assertIn('fable verified the named passage; astra could not open it.', text)
            self.assertIn('astra verified the named passage; fable could not open it.', text)
            self.assertEqual(state, original)
            rendered.append(text)
        self.assertEqual(rendered[0], rendered[1])

    def test_shared_blocking_id_preserves_both_reviewers_reasons(self):
        reports = {family: envelope(family, review=report(decision='changes_requested', prior_findings=[{
            'id': 'prior-F1', 'resolution': 'unresolved', 'reason': reason}]))
            for family, reason in [('astra', 'The first premise fails.'), ('fable', 'The second premise fails.')]}
        rendered = []
        for ordered in (reports, dict(reversed(list(reports.items())))):
            text = gate.round_summary_body(self.state(conclusion='failure', reports=ordered), 'x/y', 'check')
            self.assertIn('The first premise fails.', text)
            self.assertIn('The second premise fails.', text)
            self.assertIn('"blocking_count": 1', text)
            rendered.append(text)
        self.assertEqual(*rendered)

    def test_interruption_does_not_invent_mathematical_error(self):
        text = gate.round_summary_body(self.state(conclusion='failure', reports={'astra': envelope(complete=False)}), 'x/y', 'check')
        self.assertIn('Astra: did not complete', text)
        self.assertIn('not a mathematical error', text)

    def test_long_summaries_link_full_records_without_altering_findings(self):
        findings = [{'id': 'F'+str(i), 'objection': 'x'*5000} for i in range(50)]
        state = self.state(conclusion='failure', reports={'astra': envelope(review=report(decision='changes_requested', findings=findings))})
        text = gate.round_summary_body(state, 'x/y', 'check')
        self.assertLess(len(text.encode()), 12000)
        self.assertIn('40 more entries', text)
        self.assertEqual(len(state['reports']['astra']['review']['findings']), 50)

    def test_existing_comment_prevents_duplicate_post(self):
        gh = FakeGH()
        state = self.state()
        gh.comments = [comment(gate.round_summary_body(state, 'x/y', 'check'))]
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)):
            gate.post_round_summary(gh, state, {})
        self.assertEqual(gh.posts, [])

    def test_own_summary_does_not_force_another_history_review(self):
        gh = FakeGH()
        gh.comments = [comment(gate.round_summary_body(self.state(), 'x/y', 'check'))]
        self.assertEqual(gate.history(gh, gh.pr)[0], [])
        gh.comments[0]['user'] = {'login': 'outside-user', 'type': 'User'}
        self.assertTrue(gate.history(gh, gh.pr)[0])

    def test_pipeline_posts_one_readable_summary(self):
        gh, app, errors, state = run_pipeline()
        self.assertEqual(errors, [])
        summaries = [p for p in gh.posts if p.get('body', '').startswith(gate.SUMMARY_MARKER)]
        self.assertEqual(len(summaries), 1)
        self.assertEqual(app.final['conclusion'], 'success')

    def test_unresolved_prior_finding_keeps_its_full_id(self):
        prior = [{'id': 'older-run-astra-F9', 'resolution': 'unresolved',
                  'reason': 'The denominator can be zero.'},
                 {'id': 'older-run-astra-F8', 'resolution': 'resolved',
                  'reason': 'The missing case is now proved.'}]
        text = gate.round_summary_body(self.state(conclusion='failure', reports={
            'astra': envelope(review=report(decision='changes_requested', prior_findings=prior))}), 'x/y', 'check')
        self.assertIn('older-run-astra-F9', text)
        self.assertNotIn('older-run-astra-F8', text)

    def test_comment_failure_does_not_invalidate_the_app_acceptance(self):
        with patch.object(gate, 'post_round_summary', side_effect=OSError('Comment service unavailable')):
            _, app, errors, _ = run_pipeline()
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')


if __name__ == '__main__':
    unittest.main()
