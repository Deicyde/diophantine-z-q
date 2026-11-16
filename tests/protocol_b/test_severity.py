import copy
import json
import os
import unittest
from unittest.mock import patch

from test_gate import gate, FakeGH, HEAD, envelope, report, report_comment, run_pipeline


def summary_state(**changes):
    return {'number': 1, 'head': HEAD, 'check': 20, 'conclusion': 'success',
            'reports': {'astra': envelope(), 'fable': envelope('fable')}, **changes}


def finding(**changes):
    return {'id': 'N1', 'severity': 'note', 'kind': 'editorial',
            'location': 'p.tex:12', 'objection': 'The same valid argument would be clearer with this optional sentence.',
            'attempted_resolution': '', **changes}


class Severity(unittest.TestCase):
    def pair(self, **changes):
        return {'astra': envelope(review=report(findings=[finding()], **changes)),
                'fable': envelope('fable')}

    def test_notes_can_accompany_acceptance_and_do_not_become_prior_blockers(self):
        value = report(findings=[finding()])
        self.assertEqual(gate.validate_review(value, set(), {}), value)
        pair = self.pair()
        original = copy.deepcopy(pair)
        self.assertEqual(gate.combined_decision(pair), (True, []))
        gh = FakeGH()
        gh.comments = [report_comment(e) for e in pair.values()]
        self.assertEqual(gate.history(gh, gh.pr)[1], {})
        self.assertEqual(pair, original)

    def test_note_only_completed_rejection_is_not_a_merge_condition(self):
        pair = self.pair(decision='changes_requested')
        self.assertEqual(gate.combined_decision(pair), (True, []))
        self.assertEqual(pair['astra']['review']['decision'], 'changes_requested')

    def test_unread_work_is_not_accepted_merely_because_findings_are_notes(self):
        for flags in ({'scope_complete': False},):
            pair = self.pair(decision='changes_requested', **flags)
            self.assertFalse(gate.combined_decision(pair)[0])
            with self.assertRaisesRegex(ValueError, 'scope-1-1-astra'):
                gate.overridden_decision(pair, {}, HEAD)
        pair = self.pair(decision='changes_requested')
        pair['astra']['finished_early'] = True
        self.assertFalse(gate.combined_decision(pair)[0])

    def test_incomplete_review_cannot_report_acceptance(self):
        with self.assertRaisesRegex(ValueError, 'Incomplete review cannot accept'):
            gate.validate_review(report(scope_complete=False), set(), {})

    def test_substantive_errors_and_named_gaps_still_block(self):
        for kind in ('error', 'gap', 'source_access'):
            value = report(decision='changes_requested', findings=[finding(
                severity='blocking', kind=kind,
                attempted_resolution='Checked the prior lemma and its hypotheses; it supplies no estimate for the omitted zero case.')])
            gate.validate_review(value, set(), {})
            pair = self.pair()
            pair['astra']['review'] = value
            self.assertFalse(gate.combined_decision(pair)[0])

    def test_gap_without_an_attempt_is_not_silently_downgraded(self):
        value = report(decision='changes_requested', findings=[finding(severity='blocking', kind='gap')])
        with self.assertRaisesRegex(ValueError, 'gap needs the attempted'):
            gate.validate_review(value, set(), {})
        self.assertEqual(value['findings'][0]['severity'], 'blocking')

    def test_error_cannot_be_labelled_a_note(self):
        with self.assertRaisesRegex(ValueError, 'Only editorial'):
            gate.validate_review(report(findings=[finding(kind='error')]), set(), {})

    def test_legacy_reports_keep_blocking_semantics(self):
        pair = self.pair(decision='changes_requested')
        pair['astra']['review']['findings'] = [{'id': 'F1', 'location': 'p:1', 'objection': 'An old unresolved error'}]
        self.assertFalse(gate.combined_decision(pair)[0])
        gh = FakeGH()
        gh.comments = [report_comment(pair['astra'])]
        self.assertIn('1-1-astra-F1', gate.history(gh, gh.pr)[1])

    def test_existing_unresolved_finding_does_not_disappear_among_notes(self):
        pair = self.pair(decision='changes_requested', prior_findings=[{
            'id': 'previous-F1', 'resolution': 'unresolved', 'reason': 'The contradiction remains.'}])
        self.assertFalse(gate.combined_decision(pair)[0])

    def test_summary_shows_notes_separately_and_neutralizes_mentions(self):
        state = summary_state(reports=self.pair())
        state['reports']['astra']['review']['findings'][0]['objection'] = 'Optional sentence mentioning @reader.'
        text = gate.round_summary_body(state, 'x/y', 'check')
        self.assertIn('"blocking_count": 0', text)
        self.assertIn('"nonblocking_count": 1', text)
        self.assertIn('@\u200breader', text)
        self.assertNotIn('@reader', text)

    def test_backlog_is_durable_deduplicated_and_keeps_full_note(self):
        gh = FakeGH()
        gh.call = lambda path, method='GET', data=None: (
            {'state': 'open'} if path == '/issues/50' and method == 'GET'
            else FakeGH.call(gh, path, method, data))
        state = summary_state(reports=self.pair())
        with patch.dict(os.environ, {'NOTES_ISSUE': '50'}), patch.object(gate, 'record'):
            gate.publish_notes_backlog(gh, state, {})
            self.assertEqual(len(gh.posts), 1)
            self.assertIn(finding()['objection'], gh.posts[0]['body'])
            gh.comments = [{'body': gh.posts[0]['body'], 'user': {'login': 'github-actions[bot]'}}]
            gate.publish_notes_backlog(gh, state, {})
            self.assertEqual(len(gh.posts), 1)

    def test_no_notes_means_no_backlog_request(self):
        gh = FakeGH()
        with patch.object(gh, 'call', side_effect=AssertionError('No request expected')):
            gate.publish_notes_backlog(gh, summary_state(), {})

    def test_backlog_batches_notes_and_deduplicates_each_marker(self):
        gh = FakeGH()
        gh.call = lambda path, method='GET', data=None: (
            {'state': 'open'} if path == '/issues/50' and method == 'GET'
            else FakeGH.call(gh, path, method, data))
        pair = self.pair()
        pair['astra']['review']['findings'] = [finding(id='N'+str(i)) for i in range(20)]
        state = summary_state(reports=pair)
        with patch.dict(os.environ, {'NOTES_ISSUE': '50'}), patch.object(gate, 'record'):
            gate.publish_notes_backlog(gh, state, {})
            self.assertEqual(len(gh.posts), 1)
            self.assertEqual(gh.posts[0]['body'].count('<!-- protocol-b-note:'), 20)
            gh.comments = [{'body': gh.posts[0]['body'], 'user': {'login': 'github-actions[bot]'}}]
            pair['astra']['review']['findings'].append(finding(id='N20'))
            gate.publish_notes_backlog(gh, state, {})
            self.assertEqual(len(gh.posts), 2)
            self.assertEqual(gh.posts[1]['body'].count('<!-- protocol-b-note:'), 1)

    def test_long_notes_cannot_overflow_app_or_block_reused_review(self):
        pair = self.pair(decision='changes_requested')
        pair['astra']['review']['findings'][0]['objection'] = 'optional wording ' * 2400
        pair['fable']['review']['findings'] = [finding(objection='optional wording ' * 2400)]
        before = copy.deepcopy(pair)
        text = gate.decision_text(summary_state(reports=pair), pair, [])
        self.assertLess(len(text.encode()), 6000)
        saved = json.loads(text)['reports']
        self.assertEqual(saved['astra']['review']['decision'], 'changes_requested')
        self.assertEqual(saved['astra']['nonblocking_notes_omitted']['count'], 1)
        self.assertEqual(gate.combined_decision(saved), (True, []))
        self.assertEqual(pair, before)

    def test_pipeline_retains_note_and_accepts_even_if_backlog_unavailable(self):
        def provider(reviewer):
            reviewer.history_read = True
            reviewer.reads = [{'path': 'p.tex', 'revision': HEAD, 'start': 1, 'count': 1}]
            return report(findings=[finding()])
        with patch.dict(os.environ, {'NOTES_ISSUE': ''}):
            gh, app, errors, state = run_pipeline(provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertEqual(state['reports']['astra']['review']['findings'][0], finding())
        self.assertTrue(any('Nonblocking observations' in p['body'] for p in gh.posts))


if __name__ == '__main__':
    unittest.main()
