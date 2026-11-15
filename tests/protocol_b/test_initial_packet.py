"""Oversized unsent patches are deferred, not dropped from the review scope."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from test_gate import gate, FakeGH, changed, run_pipeline, report, envelope


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
        self.assertIs(review.initial_packet['patches_deferred'], False)
        self.assertEqual(review.initial_packet['deferred_patch_count'], 0)

    def test_deferred_packet_warns_about_merge_base_coordinates(self):
        gh, review, _ = self.make()
        gh.comparison['merge_base_commit']['sha'] = 'c' * 40
        self.prepare(review)
        self.assertEqual(review.input['merge_base'], 'c' * 40)
        self.assertEqual(review.initial_packet['merge_base'], 'c' * 40)
        for item in review.input['files']:
            self.assertIn('Old hunk ranges refer to the PR merge base', item['patch_omitted'])
            self.assertIn('not necessarily the base tip served by read_file(base)', item['patch_omitted'])
            self.assertIn('report the limitation', item['patch_omitted'])
        with patch.object(gh, 'text', return_value='shifted base text') as fetch:
            review.tool('read_file', {'path':'p0.tex','revision':'base','start':1,'count':1})
            fetch.assert_called_once_with('p0.tex', gh.pr['base']['sha'])

    def test_deferral_marker_survives_durable_report_and_binding_omission(self):
        gh, _, files = self.make()
        pages = gh.pages
        gh.pages = lambda path: files if path.endswith('/files') else pages(path)
        gh.pr['changed_files'] = len(files)
        def provider(review):
            review.prepare_initial_input()
            review.tool('read_history', {})
            review.tool('read_file', {'path':'p0.tex','revision':'head','start':1,'count':1})
            return report()
        _, app, errors, state = run_pipeline(gh=gh, provider=provider)
        self.assertEqual(errors, [])
        published = json.loads(app.final['output']['text'])['reports']
        for family in gate.MODELS:
            marker = state['reports'][family]['initial_packet']
            self.assertIs(marker['patches_deferred'], True)
            self.assertEqual(marker['deferred_patch_count'], len(files))
            self.assertEqual(published[family]['initial_packet'], marker)
            self.assertTrue(any('"initial_packet"' in post['body'] and
                                '"patches_deferred": true' in post['body'] for post in gh.posts))
            large = envelope(family, initial_packet=marker, reuse_binding={'large':'x' * 61_000})
            with patch.object(gate, 'record'):
                compact = gate.bounded_report(large)
            self.assertIsNone(compact['reuse_binding'])
            self.assertEqual(compact['initial_packet'], marker)

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

    def test_changed_untracked_merge_base_context_cannot_reuse_deferred_review(self):
        old_text, new_text = 'o' * 230_000, 'n' * 230_000
        files = [changed('p.tex', '@@ -1 +1 @@\n-' + old_text + '\n+' + new_text)]
        gh, review, _ = self.make(files=files)
        old_head, old_base = gh.pr['head']['sha'], gh.pr['base']['sha']
        old_merge_base, new_merge_base = 'c' * 40, 'd' * 40
        gh.comparison['merge_base_commit']['sha'] = old_merge_base
        gh.text = lambda path, ref: ((old_text if ref in {old_merge_base, new_merge_base, old_base} else new_text)
                                    + '\n' + ('necessary old hypothesis' if ref == old_merge_base else 'changed hypothesis'))
        self.prepare(review)
        self.assertIs(review.initial_packet['patches_deferred'], True)
        with self.assertRaisesRegex(ValueError, 'cross-head reuse disabled'):
            gate.make_reuse_binding(gh, gh.pr, files, review)
        with patch.object(gate, 'record'):
            self.assertIsNone(gate.optional_reuse_binding(gh, gh.pr, files, review))
        # Reconstruct the earlier encoding: the web-only second line is absent
        # from its dependencies. The complete PR diff itself is unchanged.
        with patch.object(review, 'initial_packet', None):
            old_binding = gate.make_reuse_binding(gh, gh.pr, files, review)
        prior = envelope(head=old_head, base=old_base, initial_packet=review.initial_packet,
                         reuse_binding=old_binding)
        gh.pr['head']['sha'] = 'e' * 40
        gh.pr['base']['sha'] = new_merge_base
        gh.comparison['merge_base_commit']['sha'] = new_merge_base
        self.assertEqual(gate.diff_identity(files), old_binding['diff'])
        self.assertNotEqual(gh.text('p.tex', old_merge_base), gh.text('p.tex', new_merge_base))
        self.assertTrue(gate.reusable_on_rebase(gh, gh.pr, files, {**prior, 'initial_packet': None}))
        self.assertFalse(gate.reusable_on_rebase(gh, gh.pr, files, prior))


if __name__ == '__main__':
    unittest.main()
