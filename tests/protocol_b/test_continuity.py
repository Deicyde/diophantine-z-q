"""Exercise actual gate reuse and passage-specific access limitations offline."""
import copy
import json
import os
import unittest
import urllib.error
from unittest.mock import Mock, patch
from test_gate import gate, FakeGH, FakeApp, HEAD, BASE, APP_ID, report, envelope, comment, report_comment, changed, run_pipeline


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
            self.assertTrue(state['reports']['astra']['history_digest'])

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

    def test_supplement_keeps_full_proof_dependencies(self):
        gh=FakeGH()
        gh.text=lambda path,ref: 'proof dependency\nsecond line'
        full=gate.Review(gh,gh.pr,[],[],{},{},'instructions','astra','local mathematical')
        full.tool('read_file',{'path':'dependency.tex','revision':'head','start':1,'count':1})
        original=gate.make_reuse_binding(gh,gh.pr,[],full)
        supplement=gate.Review(gh,gh.pr,[],[],{},{},'instructions','astra','local mathematical')
        supplement.tool('read_file',{'path':'supplement.tex','revision':'head','start':2,'count':1})
        current=gate.make_reuse_binding(gh,gh.pr,[],supplement)
        inherited=gate.inherit_reuse_binding(current,accepting(reuse_binding=original))
        self.assertEqual({p['path'] for p in inherited['passages']},{'dependency.tex','supplement.tex'})
        prior=accepting(reuse_binding=inherited)
        old_head=gh.pr['head']['sha']
        gh.pr['head']['sha']='d'*40
        old_text=gh.text
        gh.text=lambda p,r: 'changed dependency\nsecond line' if p=='dependency.tex' and r!=old_head else old_text(p,r)
        self.assertFalse(gate.reusable_on_rebase(gh,gh.pr,[],prior))
        self.assertIsNone(gate.inherit_reuse_binding(current,accepting()))

    def test_rebase_fetches_each_file_revision_once(self):
        gh=FakeGH()
        gh.text=Mock(return_value='first\nsecond\nthird')
        full=gate.Review(gh,gh.pr,[],[],{},{},'instructions','astra','local mathematical')
        for start in (1,2):
            full.tool('read_file',{'path':'p.tex','revision':'head','start':start,'count':1})
        binding=gate.make_reuse_binding(gh,gh.pr,[],full)
        gh.text.reset_mock()
        gh.pr['head']['sha']='d'*40
        self.assertTrue(gate.reusable_on_rebase(gh,gh.pr,[],accepting(reuse_binding=binding)))
        self.assertEqual(gh.text.call_count,2)

    def test_original_duplicate_cannot_be_mistaken_for_edited_occurrence(self):
        gh=FakeGH()
        old='duplicate\nseparator\nduplicate'
        gh.text=lambda p,r: old
        reviewer=gate.Review(gh,gh.pr,[],[],{},{},'instructions','astra','local mathematical')
        reviewer.tool('read_file',{'path':'dependency.tex','revision':'head','start':1,'count':1})
        binding=gate.make_reuse_binding(gh,gh.pr,[],reviewer)
        gh.pr['head']['sha']='d'*40
        gh.text=lambda p,r: old if r==HEAD else 'edited\nseparator\nduplicate'
        self.assertFalse(gate.reusable_on_rebase(gh,gh.pr,[],accepting(reuse_binding=binding)))

    def test_nonreusable_later_rejection_never_revives_old_acceptance(self):
        gh,app=self.rebased()
        prior=json.loads(app.checks[5]['output']['text'])['reports']
        carried=copy.deepcopy(prior['astra']);carried['reused_for']='e'*40
        stored(app,gh,{'astra':carried},ident=6,head='e'*40)
        binding=copy.deepcopy(carried['reuse_binding'])
        binding['sources'].append({'path':'new-dependency.pdf','revision':'head','sha':'c'*40})
        rejected=accepting(head='e'*40,review=report(decision='changes_requested',
            findings=[{'id':'F1','location':'new-dependency:1','objection':'Withdraw acceptance'}]),
            reuse_binding=binding)
        stored(app,gh,{'astra':rejected},ident=8,head='e'*40)
        original=gh.call
        gh.call=lambda p,*a,**k: {'type':'file','sha':'f'*40} if p.startswith('/contents/new-dependency.pdf') else original(p,*a,**k)
        called=[]
        def run(reviewer):
            called.append(reviewer.family)
            return report()
        _,_,errors,_=run_pipeline(gh,app,event=self.command(gh),provider=run)
        self.assertEqual(errors,[])
        self.assertEqual(called,['astra'])

    def test_successive_supplements_keep_both_families_text_and_pdf_dependencies(self):
        gh=FakeGH()
        gh.text=lambda p,r: 'one\ntwo\nthree'
        envelopes={}
        for family in gate.MODELS:
            reviewer=gate.Review(gh,gh.pr,[],[],{},{},'instructions',family,'local mathematical')
            reviewer.tool('read_file',{'path':'original.tex','revision':'head','start':1,'count':1})
            reviewer.tool('read_file',{'path':'original.pdf','revision':'head','start':1,'count':1})
            retained=accepting(family,reuse_binding=gate.make_reuse_binding(gh,gh.pr,[],reviewer))
            for start in (2,3):
                supplement=gate.Review(gh,gh.pr,[],[],{},{},'instructions',family,'local mathematical')
                supplement.tool('read_file',{'path':'later.tex','revision':'head','start':start,'count':1})
                retained=accepting(family,reuse_binding=gate.inherit_reuse_binding(
                    gate.make_reuse_binding(gh,gh.pr,[],supplement),retained))
            envelopes[family]=retained
        gh.pr['head']['sha']='d'*40
        original=gh.call
        gh.call=lambda p,*a,**k: {'type':'file','sha':'f'*40} if p.startswith('/contents/original.pdf') else original(p,*a,**k)
        for e in envelopes.values():
            self.assertFalse(gate.reusable_on_rebase(gh,gh.pr,[],e))
        gh.call=original
        gh.text=lambda p,r: 'changed\ntwo\nthree' if p=='original.tex' and r=='d'*40 else 'one\ntwo\nthree'
        for e in envelopes.values():
            self.assertFalse(gate.reusable_on_rebase(gh,gh.pr,[],e))

    def test_large_optional_binding_does_not_discard_verdict(self):
        for size in (90_000,25_000):
            gh,app=FakeGH(),FakeApp()
            review=report(not_outside_reviewed=['unrelated scope note '+ 'x'*20_000])
            with patch.object(gate,'make_reuse_binding',return_value={'version':2,'padding':'x'*size}):
                _,app,errors,state=run_pipeline(gh,app,provider=Mock(return_value=review))
            self.assertEqual(errors,[])
            payload=json.loads(app.final['output']['text'])
            self.assertLess(len(app.final['output']['text'].encode()),60_000)
            for family in gate.MODELS:
                e=payload['reports'][family]
                self.assertTrue(e['complete'])
                self.assertEqual(e['review']['decision'],'accept')
                self.assertIsNone(e['reuse_binding'])
                self.assertEqual(e['review']['not_outside_reviewed'],review['not_outside_reviewed'])
                self.assertFalse(gate.reusable_on_rebase(gh,gh.pr,[],e))
            for posted in gh.posts:
                self.assertLess(len(posted['body'].encode()),65_536)

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

    def rebased_without_future_binding(self):
        gh, app = self.rebased()
        value = json.loads(app.checks[5]['output']['text'])
        for e in value['reports'].values():
            e['reuse_binding']['padding'] = 'x' * 70_000
        value['reports']['fable']['review'] = report(decision='changes_requested',
            findings=[{'id': 'gap', 'location': 'p.tex:1', 'objection': 'A gap.'}])
        app.checks[5]['output']['text'] = json.dumps(value)
        provider = Mock(side_effect=AssertionError('No repeated proof review on unchanged rebase'))
        _, _, errors, state = run_pipeline(gh, app, provider=provider)
        self.assertEqual(errors, ['Protocol B review is blocked', 'Protocol B review is blocked'])
        provider.assert_not_called()
        pair = json.loads(app.final['output']['text'])['reports']
        self.assertEqual(app.final['conclusion'], 'failure')
        for e in pair.values():
            self.assertEqual(e['reused_for'], HEAD)
            self.assertNotEqual(e['head'], HEAD)
            self.assertIsNone(e['reuse_binding'])
        stored(app, gh, pair, ident=21)
        gh.comments.extend(report_comment(e) for e in pair.values())
        return gh, app

    def test_authenticated_effective_head_retained_after_binding_omitted(self):
        gh, app = self.rebased_without_future_binding()
        called = []
        def run(reviewer):
            called.append(reviewer.family)
            return report(prior_findings=[{'id': '1-1-fable-gap', 'resolution': 'resolved',
                                           'reason': 'The clarification settles it.'}])
        _, _, errors, state = run_pipeline(gh, app, event=self.command(gh), provider=run)
        self.assertEqual(errors, [])
        self.assertEqual(called, ['fable'])
        self.assertEqual(state['reports']['astra']['head'], 'd' * 40)
        self.assertEqual(state['reports']['astra']['reused_for'], HEAD)
        self.assertIsNone(state['reports']['astra']['reuse_binding'])

    def test_effective_head_override_after_binding_omitted_calls_no_model(self):
        gh, app = self.rebased_without_future_binding()
        gh.permission = 'write'
        command = comment('/protocol-b override ' + HEAD + ' 1-1-fable-gap accepted limitation', 'collaborator')
        gh.comments.append(command)
        provider = Mock(side_effect=AssertionError('No model during authorized override'))
        event = {'issue': {'number': 1}, 'comment': command, 'sender': {'login': 'collaborator'}}
        _, _, errors, state = run_pipeline(gh, app, event=event, provider=provider)
        self.assertEqual(errors, [])
        provider.assert_not_called()
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertIn('NOT outside reviewed', state['summary'])

    def test_omitted_binding_does_not_authorize_next_head(self):
        gh, app = self.rebased_without_future_binding()
        gh.pr['head']['sha'] = 'f' * 40
        provider = Mock(return_value=report(prior_findings=[{'id': '1-1-fable-gap',
            'resolution': 'resolved', 'reason': 'Checked again on the new head.'}]))
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

    def test_unrelated_supplement_keeps_authenticated_source_evidence(self):
        gh, app = Continuity().rebased()
        value = json.loads(app.checks[5]['output']['text'])
        source = self.pair()
        # Astra verifies the source; Fable has an access-only objection.
        value['reports']['astra']['review'] = source['fable']['review']
        value['reports']['fable']['review'] = source['astra']['review']
        app.checks[5]['output']['text'] = json.dumps(value)
        gh.comments.extend(report_comment(e) for e in value['reports'].values())
        gh.comments.append(comment('A separate clarification needs examination.', 'reader'))
        called = []
        def run(reviewer):
            called.append(reviewer.family)
            reviewer.history_read = True
            reviewer.reads = [{'path': 'clarification.tex', 'revision': HEAD, 'start': 1, 'count': 1}]
            return report(source_checks=[], prior_findings=[{'id': '1-1-fable-F1',
                'resolution': 'resolved', 'reason': 'The retained source inspection covers this access limitation.'}])
        _, _, errors, state = run_pipeline(gh, app, provider=run)
        self.assertEqual(errors, [])
        self.assertEqual(called, ['astra'])
        self.assertEqual(app.final['conclusion'], 'success')
        e = state['reports']['astra']
        self.assertEqual(e['review']['source_checks'], [])  # No invented fresh inspection.
        evidence = gate.source_evidence(e)
        self.assertEqual(evidence[0]['origin']['head'], 'd' * 40)
        self.assertEqual(evidence[0]['origin']['reviewer'], 'astra')
        self.assertEqual(state['source_access_limitations'][0]['reviewer_who_checked'], 'astra')

    def test_later_source_withdrawal_supersedes_inherited_verification(self):
        pair = self.pair()
        original = pair['fable']
        retained = gate.source_evidence(original)
        withdrawn = copy.deepcopy(original['review']['source_checks'][0])
        withdrawn.update(outcome='unavailable', detail='Earlier verification is withdrawn; source not verified.')
        pair['fable'] = accepting('fable', run='2', retained_source_evidence=retained,
                                 review=report(source_checks=[withdrawn]))
        self.assertFalse(gate.combined_decision(pair)[0])
        # A later unrelated supplement must retain the withdrawal, not revive run 1.
        prior = pair['fable']
        pair['fable'] = accepting('fable', run='3', retained_source_evidence=gate.source_evidence(prior))
        self.assertFalse(gate.combined_decision(pair)[0])
        self.assertEqual(gate.source_evidence(pair['fable'])[0]['origin']['run'], '2')

    def test_history_exposes_retained_source_provenance(self):
        gh = FakeGH()
        original = self.pair()['fable']
        supplement = accepting('fable', run='2', retained_source_evidence=gate.source_evidence(original))
        gh.comments = [report_comment(supplement)]
        discussion, _, _, _ = gate.history(gh, gh.pr)
        self.assertEqual(discussion[0]['review_source_checks'][0]['outcome'], 'verified')
        self.assertEqual(discussion[0]['review_source_evidence'][0]['origin']['run'], '1')

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
