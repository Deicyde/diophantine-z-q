"""Oversized unsent patches are deferred, not dropped from the review scope."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from test_gate import gate, FakeGH, changed


class InitialPacket(unittest.TestCase):
    def make(self, family='astra', files=None):
        gh = FakeGH()
        if files is None:
            files = [changed(f'p{i}.tex', '@@ -1 +1 @@\n-old\n+' + 'x' * 120_000)
                     for i in range(4)]
        review = gate.Review(gh, gh.pr, files, [], {}, {}, 'trusted', family, 'new result or route')
        return gh, review, files

    def prepare(self, review):
        with patch.object(gate, 'record'):
            review.prepare_initial_input()

    def test_large_initial_packet_keeps_every_file_and_all_nonpatch_metadata(self):
        for family in gate.MODELS:
            gh, review, files = self.make(family)
            original = copy.deepcopy(files)
            self.prepare(review)
            self.assertEqual(files, original)
            self.assertEqual(len(review.input['files']), len(files))
            for source, sent in zip(files, review.input['files']):
                self.assertEqual({k:v for k,v in sent.items() if k not in {'patch_omitted','patch_hunks'}},
                                 {k:v for k,v in source.items() if k != 'patch'})
                self.assertEqual(sent['patch_hunks'], ['@@ -1 +1 @@'])
                self.assertIn('Deferred', sent['patch_omitted'])
            conversation = [{'role':'user','content':json.dumps(review.input)}]
            observation = gate.context_estimate(family, 'trusted', conversation)
            self.assertLess(observation['estimated_total'], gate.CONTEXT_TOKEN_BUDGET)
            self.assertEqual(gate.diff_identity(files), gate.diff_identity(original))

    def test_small_packet_is_unchanged(self):
        _, review, files = self.make(files=[changed('small.tex')])
        before = copy.deepcopy(review.input)
        self.prepare(review)
        self.assertEqual(before, review.input)
        self.assertIs(review.initial_files, files)

    def test_originally_absent_patch_remains_listed_without_invented_hunks(self):
        _, review, files = self.make()
        files.append({'filename':'large.pdf','status':'added','sha':'a'*40})
        self.prepare(review)
        self.assertEqual(review.input['files'][-1], files[-1])

    def test_deferred_patch_is_not_recorded_as_a_read_but_actual_read_is(self):
        gh, review, files = self.make()
        self.prepare(review)
        binding = gate.make_reuse_binding(gh, gh.pr, files, review)
        self.assertEqual(binding['passages'], [])
        self.assertEqual(binding['diff'], gate.diff_identity(files))
        review.tool('read_file', {'path':'p0.tex','revision':'head','start':1,'count':1})
        binding = gate.make_reuse_binding(gh, gh.pr, files, review)
        self.assertTrue(any(p['path']=='p0.tex' and p['revision']=='head' for p in binding['passages']))

    def test_metadata_alone_over_budget_still_stops_before_provider(self):
        for family in gate.MODELS:
            _, review, _ = self.make(family)
            review.input['untrusted_description'] = 'x' * 500_000
            with tempfile.TemporaryDirectory() as temp, patch.object(gate, 'OUT', Path(temp)), \
                    patch.object(gate, 'model_turn') as provider:
                with self.assertRaisesRegex(RuntimeError, 'context budget exceeded'):
                    review.run()
                provider.assert_not_called()


if __name__ == '__main__':
    unittest.main()
