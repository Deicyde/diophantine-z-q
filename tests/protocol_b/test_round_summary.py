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
