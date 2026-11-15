"""Exercise actual gate reuse and passage-specific access limitations offline."""
import copy
import json
import os
import unittest
from unittest.mock import Mock, patch
from test_gate import gate, FakeGH, FakeApp, HEAD, BASE, APP_ID, report, envelope, comment, changed, run_pipeline


def stored(app, gh, reports, ident=5, head=HEAD):
    app.prior(reports, ident=ident)
    item = app.checks[ident]
    item['head_sha'] = head
    value = json.loads(item['output']['text'])
    value.update(head=head, review_round={'number': 1, 'run': str(ident), 'attempt': '1',
                                        'started': True, 'trigger': 'command'})
    item['output']['text'] = json.dumps(value)
    gh.comments.append(comment(gate.ROUND_MARKER + '\n```json\n' + json.dumps({'check': ident}) + '\n```'))


def accepting(family='astra', **kw):
    return envelope(family, read_prerequisites_complete=True, **kw)


class Continuity(unittest.TestCase):
    def command(self, gh):
        gh.permission = 'write'
        return {'issue': {'number': 1}, 'comment': comment('/protocol-b review', 'collaborator'),
                'sender': {'login': 'collaborator'}}

    def test_only_missing_reviewer_called_on_same_head_even_after_policy_update(self):
        gh, app = FakeGH(), FakeApp()
        stored(app, gh, {'astra': accepting(policy_ref='e' * 40),
                        'fable': envelope('fable', complete=False)})
        called = []
        def run(reviewer):
            called.append(reviewer.family)
            return report()
        _, _, errors, state = run_pipeline(gh, app, event=self.command(gh), provider=run)
        self.assertEqual(errors, [])
        self.assertEqual(called, ['fable'])
        self.assertEqual(state['reports']['astra']['head'], HEAD)
        self.assertEqual(state['reports']['astra']['reuse_check'], 5)
        self.assertEqual(state['conclusion'], 'success')

    def test_acceptances_in_separate_rounds_need_no_model(self):
        gh, app = FakeGH(), FakeApp()
        stored(app, gh, {'astra': accepting()}, ident=5)
        stored(app, gh, {'fable': accepting('fable')}, ident=6)
        provider = Mock(side_effect=AssertionError('No model call'))
        _, _, errors, state = run_pipeline(gh, app, event=self.command(gh), provider=provider)
        provider.assert_not_called()
        self.assertEqual(errors, [])
        self.assertEqual(state['conclusion'], 'success')
        self.assertFalse(state['review_round']['started'])

    def test_cache_metadata_error_preserves_completed_verdict(self):
        gh = FakeGH()
        original = gh.call
        def call(path, *args, **kwargs):
            if path.startswith('/contents/'):
                raise ValueError('metadata temporarily unavailable')
            return original(path, *args, **kwargs)
        gh.call = call
        _, _, errors, state = run_pipeline(gh)
        self.assertEqual(errors, [])
        self.assertEqual(state['conclusion'], 'success')
        self.assertIsNone(state['reports']['astra']['reuse_binding'])

    def test_forged_app_wrong_pr_and_incomplete_cannot_supply_reuse(self):
        for mutation in ['app', 'number', 'incomplete', 'model']:
            gh, app = FakeGH(), FakeApp()
            e = accepting()
            if mutation == 'incomplete': e['complete'] = False
            if mutation == 'model': e['model'] = 'unapproved'
            stored(app, gh, {'astra': e})
            if mutation == 'app': app.checks[5]['app']['id'] = 15368
            if mutation == 'number':
                v = json.loads(app.checks[5]['output']['text'])
                v['review_round']['number'] = 2
                app.checks[5]['output']['text'] = json.dumps(v)
            provider = Mock(return_value=report())
            _, _, errors, _ = run_pipeline(gh, app, event=self.command(gh), provider=provider)
            self.assertEqual(errors, [])
            self.assertEqual(provider.call_count, 2)

    def rebased(self):
        gh, app = FakeGH(), FakeApp()
        old_head = 'd' * 40
        reviewer = gate.Review(gh, gh.pr, [], [], {}, {}, 'instructions', 'astra', 'local mathematical')
        reviewer.reads = [{'path': 'p.tex', 'revision': HEAD, 'start': 1, 'count': 10}]
        binding = gate.make_reuse_binding(gh, gh.pr, [changed('p.tex')], reviewer)
        pair = {f: accepting(f, head=old_head, reuse_binding=copy.deepcopy(binding)) for f in gate.MODELS}
        stored(app, gh, pair, head=old_head)
        return gh, app

    def test_disjoint_rebase_reuses_both_and_binds_new_check_to_new_head(self):
        gh, app = self.rebased()
        provider = Mock(side_effect=AssertionError('No model'))
        _, app, errors, state = run_pipeline(gh, app, provider=provider)
        provider.assert_not_called()
        self.assertEqual(errors, [])
        self.assertEqual(state['head'], HEAD)
        self.assertEqual(state['reports']['astra']['head'], 'd' * 40)
        self.assertEqual(state['reports']['astra']['reused_for'], HEAD)
        self.assertEqual(app.final['conclusion'], 'success')

    def test_reuse_does_not_spend_a_fifth_automatic_round(self):
        gh, app = self.rebased()
        original = gate.review_spend_history
        def spent(*args):
            value = original(*args)
            value['automatic_rounds'] = 4
            return value
        provider = Mock(side_effect=AssertionError('No model'))
        with patch.object(gate, 'review_spend_history', side_effect=spent):
            _, _, errors, state = run_pipeline(gh, app, provider=provider)
        provider.assert_not_called()
        self.assertEqual(errors, [])
        self.assertEqual(state['automatic_rounds'], 4)

    def test_conditional_acceptance_cannot_carry_override_to_another_head(self):
        gh, app = self.rebased()
        value = json.loads(app.checks[5]['output']['text'])
        e = value['reports']['astra']
        e['review']['prior_findings'] = [{'id': 'old-F1', 'resolution': 'overridden', 'reason': 'owner'}]
        app.checks[5]['output']['text'] = json.dumps(value)
        with patch.dict(os.environ, {'APP_ID': str(APP_ID)}):
            candidates = gate.review_spend_history(gh, app, gh.pr, 'Protocol B / test review', BASE)['candidates']
            selected = gate.reusable_reports(gh, gh.pr, [changed('p.tex')], candidates, overrides={'old-F1': {}})
        self.assertNotIn('astra', selected)
        e['head'] = HEAD
        selected = gate.reusable_reports(gh, gh.pr, [changed('p.tex')], [(5, {'astra': e})])
        self.assertNotIn('astra', selected)
        selected = gate.reusable_reports(gh, gh.pr, [changed('p.tex')], [(5, {'astra': e})], overrides={'old-F1': {}})
        self.assertIn('astra', selected)

    def test_changed_diff_or_reviewed_dependency_requires_fresh_reviews(self):
        for mutation in ['diff', 'dependency']:
            gh, app = self.rebased()
            if mutation == 'diff':
                original = gh.pages
                gh.pages = lambda p: [changed('p.tex', '-alpha\n+beta')] if p.endswith('/files') else original(p)
            else:
                original = gh.call
                gh.call = lambda p, *a, **kw: {'type': 'file', 'sha': 'e' * 40} if p.startswith('/contents/') else original(p, *a, **kw)
            provider = Mock(return_value=report())
            _, _, errors, _ = run_pipeline(gh, app, provider=provider)
            self.assertEqual(errors, [])
            self.assertEqual(provider.call_count, 2)

    def test_complete_rejection_reused_on_rebase_but_explicit_command_reruns_it(self):
        for explicit in [False, True]:
            gh, app = self.rebased()
            value = json.loads(app.checks[5]['output']['text'])
            value['reports']['fable']['review'] = report(decision='changes_requested',
                findings=[{'id': 'gap', 'location': 'p.tex:1', 'objection': 'An implication is false.'}])
            app.checks[5]['output']['text'] = json.dumps(value)
            provider = Mock(return_value=report())
            _, _, errors, state = run_pipeline(gh, app, provider=provider,
                event=self.command(gh) if explicit else None)
            self.assertEqual(provider.call_count, int(explicit))
            self.assertEqual(state['conclusion'], 'success' if explicit else 'failure')

    def test_patch_positions_ignored_but_not_content_truncation_or_rename(self):
        a = changed('p.tex', '@@ -1 +1 @@\n-old\n+new')
        b = changed('p.tex', '@@ -27 +39 @@\n-old\n+new')
        self.assertEqual(gate.diff_identity([a]), gate.diff_identity([b]))
        self.assertNotEqual(gate.diff_identity([a]), gate.diff_identity([changed('q.tex', a['patch'])]))
        self.assertIsNone(gate.diff_identity([changed(additions=3)]))
        missing = changed(); missing.pop('patch')
        self.assertIsNone(gate.diff_identity([missing]))


class AccessLimitations(unittest.TestCase):
    def pair(self):
        ident = 'Nekovar 2006 Corollary 8.4.8.2(i)'
        a = report(decision='changes_requested',
            findings=[{'id': 'F1', 'location': 'p.tex:1', 'objection': 'Could not open the necessary source.'}],
            source_checks=[{'source_id': ident, 'location': 'published p. 170', 'outcome': 'unavailable',
                            'detail': 'The PDF could not be downloaded; no mathematical objection was found.'}],
            access_limitations=[{'finding_id': 'F1', 'source_ids': [ident],
                                 'detail': 'Access alone is missing; every other part of the application was checked.'}])
        b = report(source_checks=[{'source_id': ident, 'location': 'published p. 170', 'outcome': 'verified',
                                  'detail': 'Read the exact statement and checked its hypotheses, map and consumer without objection.'}])
        gate.validate_review(a, set(), {})
        gate.validate_review(b, set(), {})
        return {'astra': accepting(review=a), 'fable': accepting('fable', review=b)}

    def test_matching_peer_source_turns_only_access_finding_into_visible_limitation(self):
        accepted, limits = gate.combined_decision(self.pair())
        self.assertTrue(accepted)
        self.assertEqual(limits[0]['finding'], '1-1-astra-F1')
        self.assertEqual(limits[0]['reviewer_who_checked'], 'fable')

    def test_pipeline_publishes_source_access_limits_without_rewriting_verdict(self):
        pair = self.pair()
        def provider(reviewer):
            reviewer.history_read = True
            reviewer.reads = [{'path': 'p.tex', 'revision': HEAD, 'start': 1, 'count': 10}]
            return copy.deepcopy(pair[reviewer.family]['review'])
        _, app, errors, state = run_pipeline(provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertEqual(state['reports']['astra']['review']['decision'], 'changes_requested')
        self.assertEqual(state['source_access_limitations'][0]['reviewer_who_checked'], 'fable')
        self.assertIn('not unanimous', state['summary'])

    def test_new_undispositioned_objection_cannot_disappear_between_acceptances(self):
        pair = {'astra': accepting(), 'fable': accepting('fable')}
        self.assertFalse(gate.combined_decision(pair, {'new-F1': {}})[0])

    def test_other_source_unread_same_source_and_substantive_finding_still_block(self):
        for mode in ['other source', 'unread', 'substantive', 'unfinished']:
            pair = self.pair()
            if mode == 'other source': pair['fable']['review']['source_checks'][0]['source_id'] += ' different'
            if mode == 'unread': pair['fable']['review']['source_checks'][0]['outcome'] = 'unavailable'
            if mode == 'substantive': pair['astra']['review']['findings'].append({'id': 'F2', 'location': 'p:2', 'objection': 'False'})
            if mode == 'unfinished': pair['astra']['finished_early'] = True
            self.assertFalse(gate.combined_decision(pair)[0])

    def test_legacy_untyped_objection_is_not_guessed_from_text(self):
        pair = self.pair()
        pair['astra']['review']['access_limitations'] = []
        self.assertFalse(gate.combined_decision(pair)[0])

    def test_prior_finding_is_retained_with_original_id(self):
        pair = self.pair()
        a = pair['astra']['review']
        a['findings'] = []
        a['prior_findings'] = [{'id': 'old-run-fable-F1', 'resolution': 'unresolved', 'reason': 'Still cannot download'}]
        a['access_limitations'][0]['finding_id'] = 'old-run-fable-F1'
        gate.validate_review(a, {'old-run-fable-F1'}, {})
        accepted, limits = gate.combined_decision(pair)
        self.assertTrue(accepted)
        self.assertEqual(limits[0]['finding'], 'old-run-fable-F1')


if __name__ == '__main__':
    unittest.main()
