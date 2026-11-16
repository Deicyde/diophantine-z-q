"""Source-access relief cannot cover a later substantive occurrence of its ID."""
import copy
import json
import unittest
from unittest.mock import Mock, patch
from test_gate import gate, FakeGH, FakeApp, HEAD, report, envelope, comment, run_pipeline
from test_continuity import stored


class CarriedAccess(unittest.TestCase):
    ident = '2-1-astra-F1'

    def fixture(self, later_family='fable', reverse=False, repair=False):
        gh, app = FakeGH(), FakeApp()
        verified = {'source_id': 'S', 'location': 'Theorem 1', 'outcome': 'verified',
                    'detail': 'Opened the exact passage and checked the application.'}
        astra = envelope(run='2', read_prerequisites_complete=True, review=report(
            decision='changes_requested', findings=[
                {'id': 'F1', 'location': 'S', 'objection': 'The source could not be opened.'},
                {'id': 'G1', 'location': 'p:1', 'objection': 'A separate substantive error.'}],
            source_checks=[{**verified, 'outcome': 'unavailable', 'detail': 'Could not open the source.'}],
            access_limitations=[{'finding_id': 'F1', 'source_ids': ['S'], 'detail': 'Only source access is unavailable.'}]))
        fable = envelope('fable', run='2', read_prerequisites_complete=True,
                         review=report(source_checks=[verified]))
        pair = {'astra': astra, 'fable': fable}
        if reverse:
            pair = dict(reversed(list(pair.items())))
        stored(app, gh, pair, ident=5)
        later = envelope(later_family, run='3', head='c'*40, read_prerequisites_complete=True,
            review=report(decision='changes_requested', prior_findings=[{
                'id': self.ident, 'resolution': 'unresolved', 'reason': 'The source hypothesis is false for the supplied object.'}]))
        stored(app, gh, {later_family: later}, ident=6, head='c'*40)
        if repair:
            self.assertEqual(later_family, 'fable')
            current = copy.deepcopy(pair)
            current['fable'] = envelope('fable', run='4', read_prerequisites_complete=True,
                review=report(source_checks=[verified], prior_findings=[{
                    'id': self.ident, 'resolution': 'resolved', 'reason': 'Read the amended source; the missing hypothesis is now proved.'}]))
            stored(app, gh, current, ident=8)
        return gh, app

    def override(self, gh, app, ids):
        gh.permission = 'admin'
        gh.comments += [comment('/protocol-b override '+HEAD+' '+ident+' Explicit decision on this objection',
                                'collaborator') for ident in ids]
        event = {'issue': {'number': 1}, 'comment': gh.comments[-1], 'sender': {'login': 'collaborator'}}
        provider = Mock(side_effect=AssertionError('No model call for override'))
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No provider request')):
            result = run_pipeline(gh, app, event=event, provider=provider)
        provider.assert_not_called()
        return result

    def test_substantive_occurrence_needs_separate_decision_despite_old_access_relief(self):
        for family in gate.MODELS:
            for reverse in (False, True):
                for include_finding in (False, True):
                    with self.subTest(family=family, reverse=reverse, include_finding=include_finding):
                        gh, app = self.fixture(family, reverse)
                        gh, app, errors, state = self.override(gh, app,
                            ['2-1-astra-G1'] + ([self.ident] if include_finding else []))
                        self.assertEqual(app.final['conclusion'], 'success' if include_finding else 'failure')
                        self.assertEqual(gate.qualified_access_findings(state['reports'], include_overridden=True), [])
                        retained = next(e['carried_findings'][self.ident] for e in state['reports'].values()
                                        if self.ident in e.get('carried_findings', {}))
                        self.assertEqual(retained['origin_reviewer'], family)
                        self.assertIn('hypothesis is false', retained['reason'])
                        self.assertIn('observation', retained)
                        if include_finding:
                            self.assertEqual(errors, [])
                            self.assertIn(self.ident, state['overrides'])
                        else:
                            self.assertIn(self.ident, state['summary'])
                            self.assertFalse(gh.merge_requests)
                            # A stale summary classification also cannot hide the carried objection.
                            state['source_access_limitations'] = [{'finding': self.ident,
                                'reviewer_unable_to_open': 'astra', 'reviewer_who_checked': 'fable'}]
                            summary = gate.round_summary_body(state, 'x/y', 'check')
                            self.assertIn('hypothesis is false', summary)
                            self.assertIn('"blocking_count": 2', summary)
                            self.assertNotIn('Source access: fable verified', summary)

    def test_actual_later_resolution_restores_legitimate_access_relief(self):
        gh, app = self.fixture(repair=True)
        _, app, errors, state = self.override(gh, app, ['2-1-astra-G1'])
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertNotIn(self.ident, state['overrides'])
        self.assertEqual({x['finding'] for x in state['source_access_limitations']}, {self.ident})

    def test_carried_occurrences_keep_both_families_through_serialization(self):
        gh, app = self.fixture()
        original = json.loads(app.checks[5]['output']['text'])['reports']
        later = {family: envelope(family, run='3', head='c'*40, review=report(
            decision='changes_requested', prior_findings=[{'id': self.ident, 'resolution': 'unresolved',
                'reason': family+' identified a distinct substantive obstruction.'}])) for family in gate.MODELS}
        for ordered in (later, dict(reversed(list(later.items())))):
            current = copy.deepcopy(original)
            candidates = [(5, original), (6, ordered)]
            gate.carry_obligations(current, candidates)
            retained = next(e['carried_findings'][self.ident] for e in current.values()
                            if self.ident in e.get('carried_findings', {}))
            self.assertEqual({s['origin_reviewer'] for s in gate.obligation_sources(retained)}, set(gate.MODELS))
            copied = json.loads(json.dumps(current))
            repaired = {'astra': envelope(run='4', read_prerequisites_complete=True,
                review=report(prior_findings=[{'id': self.ident, 'resolution': 'resolved',
                    'reason': 'Only Astra has verified its objection was fixed.'}]))}
            remaining = gate.historical_obligations(candidates+[(7, copied)], repaired)[self.ident]
            self.assertEqual(remaining['origin_reviewer'], 'fable')
            self.assertIn('fable identified', remaining['reason'])


if __name__ == '__main__':
    unittest.main()
