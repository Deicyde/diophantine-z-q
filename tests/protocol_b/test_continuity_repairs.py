"""Capacity and merge-base regressions for the actual embedded gate, offline."""
import copy
import json
import unittest
from unittest.mock import patch

from test_gate import gate, FakeGH, HEAD, BASE, report, comment, report_comment, changed, run_pipeline
import test_continuity as continuity
from test_continuity import accepting


class FreshAttestationCapacity(unittest.TestCase):
    def run_fresh(self, reviews):
        saved = {}
        original_record = gate.record

        def record(name, value):
            saved[name] = copy.deepcopy(value)
            original_record(name, value)

        def provider(reviewer):
            reviewer.history_read = True
            reviewer.reads = [{'path': 'p.tex', 'revision': HEAD, 'start': 1, 'count': 1}]
            value = copy.deepcopy(reviews[reviewer.family])
            gate.validate_review(value, set(), {})
            self.assertLess(len(json.dumps(value, ensure_ascii=False).encode()), 45_000)
            return value

        with patch.object(gate, 'record', side_effect=record):
            gh, app, errors, state = run_pipeline(provider=provider)
        payload = json.loads(app.final['output']['text'])
        self.assertLessEqual(len(app.final['output']['text'].encode()), 60_000)
        self.assertTrue(all(len(post['body'].encode()) < 65_536 for post in gh.posts))
        self.assertEqual(app.final['status'], 'completed')
        for family, original in reviews.items():
            self.assertEqual(saved[family + '-report.json']['review'], original)
            published = payload['reports'][family]
            self.assertTrue(published['complete'])
            for key in ('decision', 'findings', 'prior_findings', 'not_outside_reviewed'):
                self.assertEqual(published['review'][key], original[key])
            if 'source_evidence_omitted' in published:
                omitted = saved[family + '-omitted-current-source-checks.json']
                self.assertEqual(omitted['source_checks'], original['source_checks'])
                self.assertEqual(omitted['origin']['head'], HEAD)
                self.assertEqual(gate.source_evidence(published), [])
        self.assertTrue(any('source_evidence_omitted' in e for e in payload['reports'].values()))
        return gh, app, errors, state, payload

    def large_checks(self):
        return {family: report(source_checks=[{
            'source_id': 'same published passage', 'location': 'Theorem 1, p. 2',
            'outcome': 'verified', 'detail': family + ' ' + 'x' * 35_000}])
            for family in gate.MODELS}

    def test_two_fresh_large_reports_reach_completed_success_check(self):
        _, app, errors, state, _ = self.run_fresh(self.large_checks())
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertEqual(state['conclusion'], 'success')

    def test_two_fresh_large_reports_keep_rejection_authoritative(self):
        reviews = self.large_checks()
        reviews['astra'].update(decision='changes_requested', findings=[{
            'id': 'gap', 'location': 'p.tex:1', 'objection': 'The implication has a counterexample.'}])
        gh, app, errors, _, payload = self.run_fresh(reviews)
        self.assertEqual(errors, ['Protocol B review is blocked', 'Protocol B review is blocked'])
        self.assertEqual(app.final['conclusion'], 'failure')
        selected = gate.reusable_reports(gh, gh.pr, [], [
            (1, {'astra': accepting()}), (2, payload['reports'])], explicit_review=True)
        self.assertNotIn('astra', selected)

    def test_omitting_fresh_peer_attestation_recomputes_access_relief(self):
        reviews = {f: e['review'] for f, e in continuity.AccessLimitations().pair().items()}
        reviews['astra']['source_checks'][0]['detail'] = 'Unavailable: ' + 'x' * 35_000
        reviews['fable']['source_checks'][0]['detail'] = 'Verified: ' + 'y' * 36_000
        _, app, errors, state, payload = self.run_fresh(reviews)
        self.assertEqual(errors, ['Protocol B review is blocked', 'Protocol B review is blocked'])
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertEqual(state['source_access_limitations'], [])
        self.assertEqual(payload['source_access_limitations'], [])
        self.assertFalse(gate.combined_decision(payload['reports'])[0])

    def test_omitted_withdrawal_never_reveals_inherited_verification(self):
        pair = continuity.AccessLimitations().pair()
        current = pair['fable']
        current['retained_source_evidence'] = gate.source_evidence(current)
        current['review']['source_checks'][0]['outcome'] = 'unavailable'
        current['review']['source_checks'][0]['detail'] = 'Withdrawn: ' + 'x' * 36_000
        pair['astra']['review']['source_checks'][0]['detail'] = 'Unavailable: ' + 'y' * 35_000
        with patch.object(gate, 'record') as saved:
            accepted, limits = gate.bounded_decision({'head': HEAD}, pair, {}, None)
        self.assertFalse(accepted)
        self.assertEqual(limits, [])
        self.assertEqual(gate.source_evidence(current), [])
        self.assertEqual(gate.retained_sources(current, report()), [])
        self.assertTrue(any(c.args[0] == 'fable-omitted-current-source-checks.json'
                            for c in saved.call_args_list))
        next_review = accepting('fable', run='next',
                                retained_source_evidence=gate.retained_sources(current, report()))
        self.assertFalse(gate.combined_decision({'astra': pair['astra'], 'fable': next_review})[0])

    def test_published_omitted_withdrawal_supersedes_prior_verified_report(self):
        gh, app = continuity.Continuity().rebased()
        original = json.loads(app.checks[5]['output']['text'])['reports']
        source = continuity.AccessLimitations().pair()
        original['astra']['review'] = source['fable']['review']
        original['fable']['review'] = source['astra']['review']
        original['fable']['review']['source_checks'][0]['detail'] = 'Unavailable: ' + 'x' * 35_000
        continuity.stored(app, gh, original, head='d' * 40)
        gh.comments.extend(report_comment(e) for e in original.values())
        gh.comments.append(comment('Please check the earlier source verification.', 'reader'))
        withdrawal = copy.deepcopy(original['astra']['review']['source_checks'][0])
        withdrawal.update(outcome='unavailable', detail='Earlier verification withdrawn: ' + 'y' * 36_000)
        called = []

        def provider(reviewer):
            called.append(reviewer.family)
            reviewer.history_read = True
            reviewer.reads = [{'path': 'p.tex', 'revision': HEAD, 'start': 1, 'count': 1}]
            value = report(source_checks=[withdrawal], prior_findings=[{
                'id': '1-1-fable-F1', 'resolution': 'unresolved', 'reason': 'The passage is not verified.'}],
                decision='changes_requested', access_limitations=[{
                    'finding_id': '1-1-fable-F1', 'source_ids': [withdrawal['source_id']],
                    'detail': 'The cited passage is unavailable; the earlier verification is withdrawn.'}])
            gate.validate_review(value, {'1-1-fable-F1'}, {})
            return value

        _, app, errors, state = run_pipeline(gh, app, provider=provider)
        self.assertEqual(called, ['astra'])
        self.assertEqual(errors, ['Protocol B review is blocked', 'Protocol B review is blocked'])
        self.assertEqual(app.final['status'], 'completed')
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertLessEqual(len(app.final['output']['text'].encode()), 60_000)
        published = json.loads(app.final['output']['text'])['reports']
        self.assertIn('source_evidence_omitted', published['astra'])
        self.assertEqual(gate.source_evidence(published['astra']), [])
        self.assertEqual(state['source_access_limitations'], [])
        latest = gate.reusable_reports(gh, gh.pr, [changed('p.tex')],
                                      [(5, original), (20, published)])
        self.assertEqual(published['astra']['review']['decision'], 'changes_requested')
        self.assertNotIn('astra', latest)  # Rerun the latest rejection; never revive the older verified accept.
        self.assertFalse(gate.combined_decision(latest)[0])


class MergeBasePassages(unittest.TestCase):
    def prepare(self):
        gh = FakeGH()
        merge_base = 'c' * 40
        gh.comparison['merge_base_commit']['sha'] = merge_base
        self.texts = {
            merge_base: 'heading\nreviewed context\nold value\ntail',
            BASE: 'base advanced before review\nheading\nreviewed context\nold value\ntail',
            HEAD: 'heading\nreviewed context\nnew value\ntail',
        }
        original_text = gh.text
        gh.text = lambda path, ref: self.texts[ref] if path == 'p.tex' else original_text(path, ref)
        files = [changed('p.tex', '@@ -2,3 +2,3 @@\n reviewed context\n-old value\n+new value\n tail')]
        reviewer = gate.Review(gh, gh.pr, files, [], {}, {}, 'instructions', 'astra', 'local mathematical')
        result = reviewer.tool('read_file', {'path': 'p.tex', 'revision': 'base', 'start': 3, 'count': 1})
        self.assertIn('reviewed context', result['text'])
        binding = gate.make_reuse_binding(gh, gh.pr, files, reviewer)
        self.assertEqual(binding['version'], 3)
        self.assertEqual(binding['merge_base'], merge_base)
        passages = {p['revision']: p for p in binding['passages']}
        self.assertEqual(passages['base']['ref'], BASE)
        self.assertEqual(passages['base']['start'], 3)
        self.assertEqual(passages['merge_base']['ref'], merge_base)
        self.assertEqual(passages['merge_base']['start'], 2)
        self.assertEqual(passages['head']['ref'], HEAD)
        self.assertEqual(passages['merge_base']['digest'],
                         gate.passage_digest(['reviewed context', 'old value', 'tail']))
        return gh, files, reviewer, accepting(reuse_binding=binding)

    def rebase(self, gh):
        gh.pr['base']['sha'], gh.pr['head']['sha'] = 'e' * 40, 'f' * 40
        gh.comparison['merge_base_commit']['sha'] = 'd' * 40
        self.texts.update({
            'd' * 40: 'disjoint insertion\nheading\nreviewed context\nold value\ntail',
            'e' * 40: 'later base insertion\ndisjoint insertion\nheading\nreviewed context\nold value\ntail',
            'f' * 40: 'disjoint insertion\nheading\nreviewed context\nnew value\ntail',
        })
        return [changed('p.tex', '@@ -3,3 +3,3 @@\n reviewed context\n-old value\n+new value\n tail')]

    def test_advanced_base_and_diff_merge_base_are_both_bound(self):
        gh, _, _, prior = self.prepare()
        files = self.rebase(gh)
        self.assertTrue(gate.reusable_on_rebase(gh, gh.pr, files, prior))
        self.assertIn('/compare/' + BASE + '...' + HEAD, gh.compare_requests)
        self.assertIn('/compare/' + 'e' * 40 + '...' + 'f' * 40, gh.compare_requests)

    def test_changed_or_ambiguous_source_on_either_reference_blocks_reuse(self):
        for side, mode in [('d', 'changed'), ('e', 'changed'), ('f', 'changed'),
                           ('d', 'duplicate'), ('e', 'duplicate'), ('f', 'duplicate')]:
            with self.subTest(side=side, mode=mode):
                gh, _, _, prior = self.prepare()
                files = self.rebase(gh)
                ref = side * 40
                if mode == 'changed':
                    self.texts[ref] = self.texts[ref].replace('reviewed context', 'altered context')
                else:
                    value = 'new value' if side == 'f' else 'old value'
                    self.texts[ref] += '\nreviewed context\n' + value + '\ntail'
                self.assertFalse(gate.reusable_on_rebase(gh, gh.pr, files, prior))

    def test_mismatched_initial_hunk_cannot_create_binding(self):
        gh, files, reviewer, _ = self.prepare()
        for changed_files in [
                [changed('p.tex', files[0]['patch'].replace('reviewed context', 'invented context'))],
                [changed('p.tex', files[0]['patch'].replace('-2,3', '-3,3'))]]:
            with self.subTest(patch=changed_files[0]['patch']), patch.object(gate, 'record'):
                self.assertIsNone(gate.optional_reuse_binding(gh, gh.pr, changed_files, reviewer))

    def test_missing_merge_base_and_legacy_binding_fail_closed(self):
        gh, files, reviewer, prior = self.prepare()
        prior['reuse_binding']['version'] = 2
        self.assertFalse(gate.reusable_on_rebase(gh, gh.pr, files, prior))
        gh.comparison.pop('merge_base_commit')
        with patch.object(gate, 'record'):
            self.assertIsNone(gate.optional_reuse_binding(gh, gh.pr, files, reviewer))

    def test_added_deleted_and_renamed_hunks_use_existing_side_paths(self):
        for files, contents, expected in [
                ([changed('new.tex', '@@ -0,0 +1 @@\n+new', status='added', deletions=0)],
                 {('new.tex', HEAD): 'new'}, {('new.tex', 'head')}),
                ([changed('gone.tex', '@@ -1 +0,0 @@\n-old', status='removed', additions=0)],
                 {('gone.tex', BASE): 'old'}, {('gone.tex', 'merge_base')}),
                ([changed('new.tex', '@@ -1 +1 @@\n-old\n+new', status='renamed', previous_filename='old.tex')],
                 {('old.tex', BASE): 'old', ('new.tex', HEAD): 'new'},
                 {('old.tex', 'merge_base'), ('new.tex', 'head')})]:
            with self.subTest(status=files[0]['status']):
                gh = FakeGH()
                gh.text = lambda path, ref: contents[(path, ref)]
                reviewer = gate.Review(gh, gh.pr, files, [], {}, {}, 'instructions', 'astra', 'local mathematical')
                binding = gate.make_reuse_binding(gh, gh.pr, files, reviewer)
                self.assertEqual({(p['path'], p['revision']) for p in binding['passages']}, expected)


if __name__ == '__main__':
    unittest.main()
