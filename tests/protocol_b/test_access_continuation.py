"""Continuing source-access findings retain their original full identity."""
import unittest

from test_gate import gate
import test_continuity


class ContinuingAccess(unittest.TestCase):
    def continuing(self, run='2'):
        pair = test_continuity.AccessLimitations().pair()
        old = '1-1-astra-F1'
        current = pair['astra']
        current['run'] = run
        current['review']['findings'] = []
        current['review']['prior_findings'] = [{
            'id': old, 'resolution': 'unresolved',
            'reason': 'The same source remains unavailable to this reviewer.'}]
        current['review']['access_limitations'][0]['finding_id'] = old
        return pair, old

    def test_full_earlier_id_with_peer_verification_is_nonblocking(self):
        pair, old = self.continuing()
        gate.validate_review(pair['astra']['review'], {old}, {})
        accepted, limits = gate.combined_decision(pair, prior={old: {}})
        self.assertTrue(accepted)
        self.assertEqual([item['finding'] for item in limits], [old])
        self.assertEqual(pair['astra']['review']['decision'], 'changes_requested')
        self.assertEqual(pair['astra']['review']['prior_findings'][0]['resolution'], 'unresolved')

    def test_later_rounds_keep_one_original_finding(self):
        for run in ('2', '3', '4'):
            with self.subTest(run=run):
                pair, old = self.continuing(run)
                accepted, limits = gate.combined_decision(pair, prior={old: {}})
                self.assertTrue(accepted)
                self.assertEqual([item['finding'] for item in limits], [old])
                self.assertEqual(pair['astra']['review']['findings'], [])

    def test_duplicate_new_finding_does_not_cover_unqualified_old_id(self):
        pair, old = self.continuing()
        pair['astra']['review']['findings'] = [{
            'id': 'F1', 'location': 'p.tex:1', 'objection': 'Continuation of '+old}]
        pair['astra']['review']['access_limitations'][0]['finding_id'] = 'F1'
        self.assertFalse(gate.combined_decision(pair, prior={old: {}})[0])

    def test_prior_id_still_needs_same_verified_passage(self):
        for mode in ('missing', 'different', 'unavailable'):
            with self.subTest(mode=mode):
                pair, old = self.continuing()
                checks = pair['fable']['review']['source_checks']
                if mode == 'missing':
                    checks.clear()
                elif mode == 'different':
                    checks[0]['source_id'] = 'Another theorem'
                else:
                    checks[0]['outcome'] = 'unavailable'
                self.assertFalse(gate.combined_decision(pair, prior={old: {}})[0])

    def test_separate_mathematical_objection_is_not_dismissed(self):
        pair, old = self.continuing()
        pair['astra']['review']['findings'] = [{
            'id': 'F2', 'location': 'p.tex:9',
            'objection': 'The hypothesis used in this application is false.'}]
        self.assertFalse(gate.combined_decision(pair, prior={old: {}})[0])


if __name__ == '__main__':
    unittest.main()
