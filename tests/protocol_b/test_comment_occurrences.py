"""Later unmatched prior assertions are distinct from an old ID's resolution."""
import hashlib
import json
import unittest
from unittest.mock import Mock, patch
from test_gate import gate, FakeGH, FakeApp, HEAD, report, envelope, comment, report_comment, run_pipeline
from test_continuity import accepting, stored


class CommentOccurrences(unittest.TestCase):
    original = '1-1-astra-F1'

    def setup_history(self, *, reusable=False, authenticated=False):
        gh, app = FakeGH(), FakeApp()
        old = 'c'*40
        first = envelope(head=old, review=report(decision='changes_requested', findings=[
            {'id': 'F1', 'objection': 'The denominator can vanish.'}]))
        stored(app, gh, {'astra': first}, ident=4, head=old)
        resolved = {f: accepting(f, run='2', head=HEAD if reusable else old,
            review=report(prior_findings=[{'id': self.original, 'resolution': 'resolved',
                'reason': 'The earlier repair excludes the exceptional case.'}])) for f in gate.MODELS}
        stored(app, gh, resolved, ident=5, head=HEAD if reusable else old)
        absent = {f: envelope(f, run='3', complete=False, runtime_scope_record=True,
            review=report(decision='not_reviewed', scope_complete=False, not_reviewed=['No model ran']))
            for f in gate.MODELS}
        if not reusable:
            stored(app, gh, absent, ident=6)
        reopened = envelope('fable', run='4', review=report(decision='changes_requested', prior_findings=[
            {'id': self.original, 'resolution': 'unresolved', 'reason': 'The claimed repair still fails at zero.'}]))
        occurrence = report_comment(reopened)
        occurrence.update(id=91, html_url='https://github.com/x/y/issues/1#issuecomment-91')
        gh.comments.append(occurrence)
        if authenticated:
            stored(app, gh, {'fable': reopened}, ident=7)
        else:
            stored(app, gh, {}, ident=7)
        item = reopened['review']['prior_findings'][0]
        digest = hashlib.sha256(json.dumps(item, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
        ident = 'comment-91-'+digest
        return gh, app, ident, reopened

    def review_command(self, gh):
        gh.permission = 'write'
        return {'issue': {'number': 1}, 'comment': comment('/protocol-b review', 'collaborator'),
                'sender': {'login': 'collaborator'}}

    def test_scope_only_override_cannot_cover_unmatched_prior_occurrence(self):
        for include_occurrence in (False, True):
            with self.subTest(include_occurrence=include_occurrence):
                gh, app, ident, _ = self.setup_history()
                gh.permission = 'admin'
                ids = ['scope-3-1-astra', 'scope-3-1-fable']
                if include_occurrence:
                    ids.append(ident)
                gh.comments += [comment('/protocol-b override '+HEAD+' '+i+' Explicit owner decision', 'collaborator') for i in ids]
                event = {'issue': {'number': 1}, 'comment': gh.comments[-1], 'sender': {'login': 'collaborator'}}
                provider = Mock(side_effect=AssertionError('No model call for override'))
                with patch.object(gate, 'model_turn', side_effect=AssertionError('No provider request')):
                    gh, app, errors, state = run_pipeline(gh, app, event=event, provider=provider)
                provider.assert_not_called()
                self.assertEqual(app.final['conclusion'], 'success' if include_occurrence else 'failure')
                if include_occurrence:
                    self.assertEqual(errors, [])
                    self.assertIn(ident, state['overrides'])
                else:
                    self.assertIn(ident, state['summary'])
                    self.assertFalse(gh.merge_requests)
                claims = [e['carried_findings'][ident] for e in state['reports'].values()
                          if ident in e.get('carried_findings', {})]
                self.assertEqual(claims[0]['origin_reviewer'], 'history')
                self.assertEqual(claims[0]['original_finding'], self.original)
                self.assertIn('Unverified', claims[0]['reason'])
                self.assertEqual(claims[0]['report_comment']['id'], 91)

    def test_reused_acceptances_need_both_dispositions_and_expose_provenance(self):
        for resolve in (False, True):
            with self.subTest(resolve=resolve):
                gh, app, ident, _ = self.setup_history(reusable=True)
                seen = []
                def provider(reviewer):
                    data = reviewer.tool('read_history', {})
                    claim = data['earlier_findings'][ident]
                    self.assertEqual(claim['original_finding'], self.original)
                    self.assertEqual(claim['report_comment']['id'], 91)
                    self.assertIn('retained_acceptance', reviewer.input)
                    seen.append(reviewer.family)
                    reviewer.reads = [{'path': 'p.tex', 'revision': HEAD, 'start': 1, 'count': 1}]
                    return report(decision='accept' if resolve else 'changes_requested', prior_findings=[
                        {'id': ident, 'resolution': 'resolved' if resolve else 'unresolved',
                         'reason': 'Read the actual source and tested the claimed exceptional case.'}])
                _, app, errors, _ = run_pipeline(gh, app, event=self.review_command(gh), provider=provider)
                self.assertEqual(errors, [] if resolve else ['Protocol B review is blocked']*2)
                self.assertEqual(set(seen), set(gate.MODELS))
                self.assertEqual(app.final['conclusion'], 'success' if resolve else 'failure')

    def test_authenticated_occurrence_then_completed_resolution_is_not_resurrected(self):
        gh, app, ident, _ = self.setup_history(authenticated=True)
        resolved = {f: accepting(f, run='5', review=report(prior_findings=[
            {'id': self.original, 'resolution': 'resolved', 'reason': 'Both verified the new repair.'}]))
            for f in gate.MODELS}
        stored(app, gh, resolved, ident=8)
        provider = Mock(side_effect=AssertionError('Already covered by authentic later resolution'))
        _, app, errors, state = run_pipeline(gh, app, event=self.review_command(gh), provider=provider)
        provider.assert_not_called()
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertNotIn(ident, str(state))

    def test_completed_resolution_of_claim_does_not_recreate_it(self):
        gh, app, ident, _ = self.setup_history(reusable=True)
        resolved = {f: accepting(f, run='5', review=report(prior_findings=[
            {'id': self.original, 'resolution': 'resolved', 'reason': 'Original issue remains resolved.'},
            {'id': ident, 'resolution': 'resolved', 'reason': 'Inspected the later comment and source; its premise is false.'}]))
            for f in gate.MODELS}
        stored(app, gh, resolved, ident=8)
        provider = Mock(side_effect=AssertionError('Claim already explicitly resolved'))
        _, app, errors, _ = run_pipeline(gh, app, event=self.review_command(gh), provider=provider)
        provider.assert_not_called()
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')


if __name__ == '__main__':
    unittest.main()
