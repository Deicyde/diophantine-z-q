"""Reusing an old resolution cannot erase a later App-recorded objection."""
import copy
import json
import unittest
from unittest.mock import Mock, patch
from test_gate import gate, FakeGH, FakeApp, HEAD, report, envelope, comment, run_pipeline
from test_continuity import accepting, stored


class ResolutionOrder(unittest.TestCase):
    ident = '1-1-astra-F1'

    def history(self, *, other_head=False, copy_old=False):
        gh, app = FakeGH(), FakeApp()
        first = envelope(head='c'*40, review=report(decision='changes_requested', findings=[
            {'id': 'F1', 'objection': 'The denominator may vanish.'}]))
        stored(app, gh, {'astra': first}, ident=4, head='c'*40)
        accepted = {f: accepting(f, run='2', review=report(prior_findings=[{
            'id': self.ident, 'resolution': 'resolved', 'reason': 'Earlier repair accepted.'}])) for f in gate.MODELS}
        stored(app, gh, accepted, ident=5)
        head = 'd'*40 if other_head else HEAD
        reopened = envelope('fable', run='3', head=head, complete=False,
            review=report(decision='changes_requested', scope_complete=False,
                not_reviewed=['Correction interrupted'], prior_findings=[{
                    'id': self.ident, 'resolution': 'unresolved', 'reason': 'A counterexample to the old repair.'}]))
        stored(app, gh, {'fable': reopened}, ident=6, head=head)
        if copy_old:
            stored(app, gh, copy.deepcopy(accepted), ident=8)
        gh.permission = 'write'
        event = {'issue': {'number': 1}, 'comment': comment('/protocol-b review', 'collaborator'),
                 'sender': {'login': 'collaborator'}}
        return gh, app, event, accepted, reopened

    def test_later_reopening_needs_a_supplement_not_an_old_resolved_id(self):
        for other_head in (False, True):
            for copy_old in (False, True):
                for resolve in (False, True):
                    with self.subTest(other_head=other_head, copy_old=copy_old, resolve=resolve):
                        gh, app, event, _, _ = self.history(other_head=other_head, copy_old=copy_old)
                        seen = []
                        def provider(reviewer):
                            self.assertIn(self.ident, reviewer.tool('read_history', {})['earlier_findings'])
                            self.assertIn('retained_acceptance', reviewer.input)
                            seen.append(reviewer.family)
                            reviewer.reads = [{'path': 'p.tex', 'revision': HEAD, 'start': 1, 'count': 1}]
                            # A peer's resolution still cannot close Fable's continuing objection.
                            decision = 'resolved' if resolve or reviewer.family == 'astra' else 'unresolved'
                            return report(decision='accept' if decision == 'resolved' else 'changes_requested',
                                prior_findings=[{'id': self.ident, 'resolution': decision,
                                    'reason': 'Read the source and checked the later counterexample.'}])
                        gh, app, _, state = run_pipeline(gh, app, event=event, provider=provider)
                        self.assertEqual(set(seen), set(gate.MODELS))
                        self.assertEqual(app.final['conclusion'], 'success' if resolve else 'failure')
                        if not resolve:
                            saved = json.loads(app.final['output']['text'])['reports']
                            with self.assertRaisesRegex(ValueError, self.ident):
                                gate.overridden_decision(saved, {}, HEAD)
                            self.assertFalse(gh.merge_requests)

    def test_copied_old_report_does_not_reopen_a_genuinely_resolved_finding(self):
        _, _, _, accepted, reopened = self.history()
        repaired = {f: accepting(f, run='4', review=report(prior_findings=[{
            'id': self.ident, 'resolution': 'resolved', 'reason': 'New source resolves the later counterexample.'}]))
            for f in gate.MODELS}
        candidates = [(5, accepted), (6, {'fable': reopened}), (7, repaired),
                      (8, {'fable': copy.deepcopy(reopened)})]
        self.assertEqual(gate.historical_obligations(candidates, repaired), {})

    def test_duplicate_acceptance_cannot_supersede_a_new_completed_rejection(self):
        gh, _, _, accepted, reopened = self.history()
        reopened.update(complete=True, read_prerequisites_complete=True)
        reopened['review'].update(scope_complete=True, not_reviewed=[])
        candidates = [(5, accepted), (6, {'fable': reopened}), (8, copy.deepcopy(accepted))]
        selected = gate.reusable_reports(gh, gh.pr, [], candidates, explicit_review=True)
        self.assertEqual(set(selected), {'astra'})
        self.assertIn(self.ident, gate.historical_obligations(candidates, selected))

    def test_old_head_override_does_not_erase_later_app_only_reopening(self):
        for complete in (False, True):
            for include_reopening in (False, True):
                with self.subTest(complete=complete, include_reopening=include_reopening):
                    gh, app, _, accepted, reopened = self.history(other_head=True)
                    accepted['astra']['review'].update(decision='changes_requested', findings=report(
                        findings=[{'id': 'G1', 'objection': 'A separate old-head blocker.'}])['findings'])
                    old = json.loads(app.checks[5]['output']['text'])
                    old['reports'] = accepted
                    app.checks[5]['output']['text'] = json.dumps(old)
                    if complete:
                        reopened.update(complete=True, read_prerequisites_complete=True)
                        reopened['review'].update(scope_complete=True, not_reviewed=[])
                        later = json.loads(app.checks[6]['output']['text'])
                        later['reports'] = {'fable': reopened}
                        app.checks[6]['output']['text'] = json.dumps(later)
                    gh.permission = 'admin'
                    ids = ['2-1-astra-G1'] + ([self.ident] if include_reopening else [])
                    gh.comments += [comment('/protocol-b override '+HEAD+' '+ident+' Explicit owner decision',
                                            'collaborator') for ident in ids]
                    event = {'issue': {'number': 1}, 'comment': gh.comments[-1], 'sender': {'login': 'collaborator'}}
                    provider = Mock(side_effect=AssertionError('Override cannot start models'))
                    with patch.object(gate, 'model_turn', side_effect=AssertionError('No provider request')):
                        gh, app, errors, state = run_pipeline(gh, app, event=event, provider=provider)
                    provider.assert_not_called()
                    self.assertEqual(app.final['conclusion'], 'success' if include_reopening else 'failure')
                    if include_reopening:
                        self.assertEqual(errors, [])
                        self.assertIn(self.ident, state['overrides'])
                    else:
                        self.assertIn(self.ident, state['summary'])
                        self.assertFalse(gh.merge_requests)


if __name__ == '__main__':
    unittest.main()
