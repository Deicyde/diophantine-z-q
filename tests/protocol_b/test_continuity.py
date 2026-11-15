"""Exercise actual gate reuse and passage-specific access limitations offline."""
import copy
import json
import os
import unittest
import urllib.error
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

    def test_only_missing_reviewer_called_on_same_head_with_identical_policy(self):
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

    def test_changed_policy_invalidates_same_head_acceptance(self):
        gh, app = FakeGH(), FakeApp()
        stored(app, gh, {'astra': accepting(policy_ref='e'*40)})
        original=gh.text
        gh.text=lambda p,r: 'changed policy' if r=='e'*40 else original(p,r)
        provider=Mock(return_value=report())
        _, _, errors, _=run_pipeline(gh,app,event=self.command(gh),provider=provider)
        self.assertEqual(errors,[])
        self.assertEqual(provider.call_count,2)

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
        for error in (ValueError('unavailable'), urllib.error.URLError('offline'), TimeoutError('timed out')):
            gh = FakeGH()
            original = gh.call
            def call(path, *args, **kwargs):
                if path.startswith('/contents/'):
                    raise error
                return original(path, *args, **kwargs)
            gh.call = call
            _, _, errors, state = run_pipeline(gh)
            self.assertEqual(errors, [])
            self.assertEqual(state['conclusion'], 'success')
            self.assertIsNone(state['reports']['astra']['reuse_binding'])
            self.assertTrue(state['reports']['astra']['complete'])

    def test_later_completed_rejection_supersedes_acceptance(self):
        gh, app = FakeGH(), FakeApp()
        stored(app, gh, {'astra': accepting()}, ident=5)
        stored(app, gh, {'astra': accepting(review=report(decision='changes_requested',
            findings=[{'id': 'F1', 'location': 'p:1', 'objection': 'Retracted earlier acceptance.'}]))}, ident=6)
        stored(app, gh, {'fable': accepting('fable')}, ident=7)
        called = []
        def run(reviewer):
            called.append(reviewer.family)
            return report()
        _, _, errors, _ = run_pipeline(gh, app, event=self.command(gh), provider=run)
        self.assertEqual(errors, [])
        self.assertEqual(called, ['astra'])

    def test_new_discussion_or_interrupted_observation_gets_only_supplement(self):
        for interrupted in (False, True):
            gh, app = FakeGH(), FakeApp()
            stored(app, gh, {'astra': accepting()}, ident=5)
            stored(app, gh, {'fable': accepting('fable')}, ident=6)
            if interrupted:
                working = {'reviewer': 'astra', 'head': HEAD, 'run': '8', 'attempt': '1',
                           'notes': ['The target omits an essential hypothesis.']}
                gh.comments.append(comment(gate.WORKING_MARKER+'\n```json\n'+json.dumps(working)+'\n```'))
            else:
                gh.comments.append(comment('The target omits an essential hypothesis.', 'reader'))
            seen = []
            def run(reviewer):
                seen.append(reviewer.input)
                reviewer.history_read = True
                return report()
            _, _, errors, state = run_pipeline(gh, app, event=self.command(gh), provider=run)
            self.assertEqual(errors, [])
            self.assertEqual(len(seen), 1)
            self.assertIn('retained_acceptance', seen[0])
            self.assertIn('only the new discussion', seen[0]['review_task'])
            self.assertTrue(state['reports']['astra']['history_coverage'])

    def test_unreviewed_history_cannot_be_combined_into_acceptance(self):
        pair = {'astra': accepting(), 'fable': accepting('fable')}
        self.assertFalse(gate.combined_decision(pair, discussion=[{'id':1,'body':'Counterexample'}])[0])

    def test_pdf_returned_by_tool_is_bound_without_counting_as_a_read(self):
        gh = FakeGH()
        reviewer = gate.Review(gh, gh.pr, [], [], {}, {}, 'instructions', 'astra', 'local mathematical')
        reviewer.tool('read_file', {'path':'paper.pdf','revision':'head','start':1,'count':1})
        self.assertFalse(reviewer.reads)
        binding = gate.make_reuse_binding(gh, gh.pr, [], reviewer)
        self.assertIn('paper.pdf', {s['path'] for s in binding['sources']})
        old = accepting(head='d'*40, reuse_binding=binding)
        original = gh.call
        gh.call = lambda p,*a,**k: {'type':'file','sha':'e'*40} if p.startswith('/contents/paper.pdf') else original(p,*a,**k)
        self.assertFalse(gate.reusable_on_rebase(gh, gh.pr, [], old))

    def test_passage_moves_but_changed_or_ambiguous_passage_does_not_reuse(self):
        gh = FakeGH()
        old_ref = HEAD
        source = 'before\nexact reviewed passage\nafter'
        gh.text = lambda path,ref: source
        reviewer = gate.Review(gh, gh.pr, [], [], {}, {}, 'instructions', 'astra', 'local mathematical')
        reviewer.tool('read_file', {'path':'p.tex','revision':'head','start':2,'count':1})
        binding = gate.make_reuse_binding(gh, gh.pr, [], reviewer)
        old = accepting(head=old_ref, reuse_binding=binding)
        gh.pr['head']['sha'] = 'd'*40
        for new, expected in [('new material\nbefore\nexact reviewed passage\nafter', True),
                              ('before\nchanged reviewed passage\nafter', False),
                              ('exact reviewed passage\nexact reviewed passage', False)]:
            gh.text = lambda path,ref: source if ref==old_ref else new
            self.assertEqual(gate.reusable_on_rebase(gh, gh.pr, [], old), expected)

    def test_initial_diff_hunks_are_bound_without_explicit_reads(self):
        gh = FakeGH()
        gh.text = lambda path,ref: 'one\ntwo\nthree'
        reviewer = gate.Review(gh, gh.pr, [], [], {}, {}, 'instructions', 'astra', 'local mathematical')
        binding = gate.make_reuse_binding(gh, gh.pr, [changed('p.tex','@@ -2 +2 @@\n-two\n+TWO')], reviewer)
        self.assertEqual({p['revision'] for p in binding['passages']}, {'head','base'})
        self.assertTrue(all(p['start']==2 and p['count']==1 for p in binding['passages']))

    def test_peer_source_ids_are_visible_in_history(self):
        gh=FakeGH()
        e=accepting(review=report(source_checks=[{'source_id':'DOI theorem 1','outcome':'verified'}]))
        gh.comments.append(comment(gate.MARKER+'\n```json\n'+json.dumps(e)+'\n```'))
        discussion, _, _, _ = gate.history(gh,gh.pr)
        self.assertEqual(discussion[0]['review_source_checks'][0]['source_id'],'DOI theorem 1')
        self.assertFalse(gate.history_coverage(discussion))

    def test_current_head_override_accepts_authenticated_reused_envelope(self):
        pair={'astra':accepting(head='d'*40,reused_for=HEAD,policy_ref='e'*40),
              'fable':accepting('fable',review=report(decision='changes_requested',
                  findings=[{'id':'F1','location':'p:1','objection':'A gap.'}]))}
        ident='1-1-fable-F1'
        with self.assertRaisesRegex(ValueError,'Uncovered'):
            gate.overridden_decision(pair,{},HEAD)
        self.assertEqual(set(gate.overridden_decision(pair,{ident:{'collaborator':'owner'}},HEAD)),{ident})

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
