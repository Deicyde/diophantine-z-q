"""Exact administrative decisions and lossless duplicate-delivery handling."""
import copy
import json
import os
import unittest
from unittest.mock import Mock, patch

from test_gate import gate, HEAD, APP_ID, FakeGH, FakeApp, envelope, report, report_comment, comment, run_pipeline
import test_admin_override as admin_fixtures
import test_delivered_closure as delivery_fixtures
from test_delivered_closure import response


class MultiItemOverrides(unittest.TestCase):
    def setup_case(self, permission='admin', ids=None):
        gh, app, event = admin_fixtures.AdminOverrides().setup_case(permission)
        import json
        pair = json.loads(app.checks[5]['output']['text'])['reports']
        pair['astra']['review']['findings'].append(report(findings=[
            {'id': 'F2', 'objection': 'A second substantive objection.'}])['findings'][0])
        app.prior(pair)
        ids = ids or ['1-1-astra-F1', '1-1-astra-F2']
        cmd = comment('/protocol-b override '+HEAD+' '+','.join(ids)+' Explicit owner decision', 'collaborator')
        gh.comments = [report_comment(e) for e in pair.values()]+[cmd]
        event['comment'] = cmd
        return gh, app, event

    def test_one_admin_comment_covers_multiple_items_without_models(self):
        gh, app, event = self.setup_case()
        provider = Mock(side_effect=AssertionError('No reviewer on an override'))
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No provider request')):
            _, app, errors, state = run_pipeline(gh, app, event=event, provider=provider)
        provider.assert_not_called()
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertEqual(set(state['overrides']), {'1-1-astra-F1', '1-1-astra-F2'})
        self.assertEqual(len({v['url'] for v in state['overrides'].values()}), 1)

    def test_nonadmins_cannot_apply_any_item_and_call_no_models(self):
        for permission in ('write', 'maintain', 'read'):
            with self.subTest(permission=permission):
                gh, app, event = self.setup_case(permission)
                self.assertEqual(gate.history(gh, gh.pr)[2], {})
                provider = Mock(side_effect=AssertionError('No reviewer'))
                with patch.object(gate, 'model_turn', side_effect=AssertionError('No provider')):
                    _, app, _, state = run_pipeline(gh, app, event=event, provider=provider)
                provider.assert_not_called()
                self.assertFalse(app.created)

    def test_edited_or_revoked_multi_override_has_no_effect(self):
        for change in ('edited', 'revoked', 'stale', 'unknown'):
            with self.subTest(change=change):
                gh, app, event = self.setup_case(ids=['1-1-astra-F1', 'unknown'] if change=='unknown' else None)
                if change=='edited':
                    event['comment']['updated_at']='later'
                elif change=='revoked':
                    gh.permission='write'
                elif change=='stale':
                    event['comment']['body']=event['comment']['body'].replace(HEAD, 'c'*40)
                self.assertFalse(gate.history(gh, gh.pr)[2])

    def test_parser_retains_legacy_and_rejects_empty_list_members(self):
        for ids in ('F1', 'F1,F2', 'F1,F1,F2'):
            parsed=gate.parse_override_command('/protocol-b override '+HEAD+' '+ids+' reason\ncontinued')
            self.assertEqual(parsed[1], list(dict.fromkeys(ids.split(','))))
            self.assertEqual(parsed[2], 'reason\ncontinued')
        for ids in (',F1', 'F1,', 'F1,,F2', 'F1, F2'):
            self.assertIsNone(gate.parse_override_command('/protocol-b override '+HEAD+' '+ids+' reason'))
        self.assertIsNone(gate.parse_override_command('/protocol-b override '+HEAD+' F1   '))

    def test_unknown_id_reply_names_comment_and_applies_nothing(self):
        gh, app, event = self.setup_case(ids=['1-1-astra-F1', 'mistyped-id'])
        provider = Mock(side_effect=AssertionError('No reviewer'))
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No provider request')):
            _, app, errors, state = run_pipeline(gh, app, event=event, provider=provider)
        provider.assert_not_called()
        self.assertTrue(errors)
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertFalse(state.get('overrides'))
        replies = [p['body'] for p in gh.posts if p.get('body', '').startswith('This override was ignored.')]
        self.assertTrue(any('Comment '+str(event['comment']['id']) in p and 'mistyped-id' in p for p in replies))

    def test_multi_override_command_does_not_create_a_discussion_objection(self):
        gh, _, _ = self.setup_case()
        self.assertEqual(gate.history_coverage([{'body':gh.comments[-1]['body']}]), set())


class DuplicateDeliveries(unittest.TestCase):
    def test_renamed_overlong_id_keeps_one_exact_objection(self):
        for family in gate.MODELS:
            with self.subTest(family=family):
                first=report(report='Short', decision='changes_requested', findings=[{
                    'id':'F1-unattended-lean-vs-rollout-restriction',
                    'location':'setup:10', 'objection':'The old rule disagrees with the new rule.'}])
                second=copy.deepcopy(first)
                second.update(report=report()['report'])
                second['findings'][0]['id']='L1-outside-lean-rollout'
                (_, app, _, state), _, count, _=delivery_fixtures.DeliveredClosure().fixture(family,
                    response(family,[first],'one'),[response(family,[second],'two')])
                self.assertEqual(count,2)
                self.assertTrue(state['reports'][family]['complete'])
                self.assertEqual(len(state['reports'][family]['review']['findings']),1)
                self.assertEqual(state['reports'][family]['review']['findings'][0]['id'],'L1-outside-lean-rollout')
                self.assertNotIn('unvalidated-', str(state['reports'][family]['review']))
                self.assertEqual(app.final['conclusion'],'failure')

    def test_distinct_objections_are_not_deduplicated(self):
        identity={'run':'7','attempt':'1','reviewer':'astra'}
        a=report(findings=[{'id':'x'*50,'objection':'First denominator may vanish.'}])
        b=report(findings=[{'id':'y'*50,'objection':'Second denominator may vanish.'}])
        value=gate.delivered_obligations([a,b,a,b],identity,{})
        self.assertEqual(len(value['findings']),2)
        self.assertEqual(len({f['id'] for f in value['findings']}),2)

    def test_full_id_and_local_id_in_one_execution_share_one_obligation(self):
        identity={'run':'7','attempt':'1','reviewer':'astra'}
        a=report(findings=[{'id':'7-1-astra-F1','objection':'Same exact objection.'}])
        b=report(findings=[{'id':'F1','objection':'Same exact objection.'}])
        value=gate.delivered_obligations([a,b],identity,{})
        self.assertEqual([f['id'] for f in value['findings']],['F1'])

    def test_changed_objection_cannot_disappear_by_renaming(self):
        identity={'run':'7','attempt':'1','reviewer':'astra'}
        a=report(findings=[{'id':'F1','objection':'The denominator vanishes.'}])
        b=report(findings=[{'id':'F2','objection':'The numerator also vanishes.'}])
        value=gate.delivered_obligations([a,b],identity,{})
        self.assertEqual([f['id'] for f in value['findings']],['F1','F2'])


    def test_reused_id_with_changed_objection_cannot_erase_the_first(self):
        first=report(report='Short',decision='changes_requested',findings=[{
            'id':'F1','location':'p:1','objection':'The denominator can vanish.'}])
        second=report(decision='changes_requested',findings=[{
            'id':'F1','location':'p:2','objection':'The endpoint case is omitted.'}])
        (_,app,_,state),_,_,_=delivery_fixtures.DeliveredClosure().fixture('astra',
            response('astra',[first],'one'),[response('astra',[second],'two')])
        value=state['reports']['astra']
        self.assertFalse(value['complete'])
        self.assertEqual(len(value['review']['findings']),2)
        self.assertIn('denominator can vanish',str(value['review']))
        self.assertIn('endpoint case is omitted',str(value['review']))
        self.assertEqual(app.final['conclusion'],'failure')

    def test_reused_id_can_finish_after_explicit_disposition(self):
        first=report(report='Short',decision='changes_requested',findings=[{
            'id':'F1','location':'p:1','objection':'The denominator can vanish.'}])
        second=report(decision='changes_requested',findings=[{
            'id':'F1','location':'p:2','objection':'The endpoint case is omitted.'}])
        third=copy.deepcopy(second)
        third['findings'][0]['id']='F2'
        third['prior_findings']=[{'id':'7-1-astra-F1','resolution':'unresolved',
                                 'reason':'The denominator objection still needs its own repair.'}]
        (_,app,_,state),_,count,_=delivery_fixtures.DeliveredClosure().fixture('astra',
            response('astra',[first],'one'),[response('astra',[second],'two'),response('astra',[third],'three')])
        value=state['reports']['astra']
        self.assertTrue(value['complete'])
        self.assertEqual(count,3)
        self.assertEqual(value['review']['prior_findings'][0]['id'],'7-1-astra-F1')
        self.assertEqual(value['review']['findings'][0]['id'],'F2')
        self.assertEqual(app.final['conclusion'],'failure')

    def test_content_generated_id_cannot_collide_with_a_reused_explicit_id(self):
        identity={'run':'7','attempt':'1','reviewer':'astra'}
        second=report(findings=[{'id':'F1','objection':'Second objection.'}])
        fallback='unvalidated-'+gate.delivered_content_key(second['findings'][0])[:24]
        first=report(findings=[{'id':fallback,'objection':'First objection.'}])
        third=report(findings=[{'id':'F1','objection':'Third objection.'}])
        value=gate.delivered_obligations([first,third,second],identity,{})
        self.assertEqual(len(value['findings']),3)
        self.assertEqual(len({f['id'] for f in value['findings']}),3)


class OriginReviewerClosure(unittest.TestCase):
    ident='1-1-astra-F1'

    def fixture(self):
        old={'astra':envelope(review=report(decision='changes_requested',findings=[
                 {'id':'F1','objection':'An earlier objection.'}])),
             'fable':envelope('fable',review=report(decision='changes_requested',prior_findings=[
                 {'id':self.ident,'resolution':'unresolved','reason':'Repair still needed.'}]))}
        # This is an automatic carry, not a second reviewer making an objection.
        old['fable']['complete']=False
        old['fable']['runtime_retained_prior_indices']=[0]
        current={'astra':envelope(run='2',read_prerequisites_complete=True,review=report(prior_findings=[
                      {'id':self.ident,'resolution':'resolved','reason':'Checked the repaired source.'}])),
                 'fable':envelope('fable',run='2',complete=False,review=report(decision='not_reviewed',
                      scope_complete=False,not_reviewed=['The provider stopped before review.']))}
        return old,current

    def test_origin_resolution_closes_old_peer_copy_but_not_scope(self):
        old,current=self.fixture()
        state={'head':HEAD,'policy_ref':'b'*40,'reports':current,'summary':'Provider stopped'}
        gate.ensure_scope_records(state,previous=old,candidates=[(5,old)])
        self.assertIn(self.ident,current['astra']['closed_by_origin'])
        self.assertTrue(state['scope_items'])
        self.assertNotIn(self.ident,gate.override_findings(current,HEAD))
        scopes={item['id']:{'reason':'Explicit scope acceptance'} for item in state['scope_items']}
        self.assertEqual(gate.overridden_decision(current,scopes,HEAD),scopes)
        self.assertEqual(current['astra']['review']['prior_findings'][0]['reason'],'Checked the repaired source.')

    def test_peer_cannot_close_originators_unresolved_finding(self):
        old,current=self.fixture()
        current['astra']['complete']=False
        current['fable']=envelope('fable',run='2',read_prerequisites_complete=True,review=report(prior_findings=[
            {'id':self.ident,'resolution':'resolved','reason':'Only the peer thinks it is fixed.'}]))
        self.assertIn(self.ident,gate.historical_obligations([(5,old)],current))

    def test_identical_genuine_disposition_is_not_a_runtime_copy(self):
        old,current=self.fixture()
        # Only position zero came from the runtime. The next identical entry
        # is an actual delivered objection and must still block.
        old['fable']['review']['prior_findings'].append(
            copy.deepcopy(old['fable']['review']['prior_findings'][0]))
        self.assertIn(self.ident,gate.historical_obligations([(5,old)],current))

    def test_completed_review_never_discards_a_marked_disposition(self):
        old,current=self.fixture()
        old['fable']['complete']=True
        self.assertIn(self.ident,gate.historical_obligations([(5,old)],current))

    def test_runtime_positions_survive_only_in_the_authenticated_app_record(self):
        old,current=self.fixture()
        state={'head':HEAD,'policy_ref':'b'*40,'reports':old}
        saved=json.loads(gate.decision_text(state,old,[]))
        self.assertEqual(saved['reports']['fable']['runtime_retained_prior_indices'],[0])
        app=FakeApp()
        app.prior(saved['reports'])
        app.checks[5]['name']=gate.CHECK
        gh=FakeGH()
        with patch.dict(os.environ,{'APP_ID':str(APP_ID)}):
            genuine=gate.trusted_reports(app,gh.pr,gate.CHECK,999)
            self.assertEqual(genuine['fable']['runtime_retained_prior_indices'],[0])
            app.checks[5]['app']['id']=APP_ID+1
            self.assertEqual(gate.trusted_reports(app,gh.pr,gate.CHECK,999),{})
        model_value=report(runtime_retained_prior_indices=[0])
        with self.assertRaisesRegex(ValueError,'Incomplete final report'):
            gate.validate_review(model_value,set(),{})

    def test_unvalidated_or_unread_origin_resolution_cannot_close(self):
        for change in ({'complete':False},{'read_prerequisites_complete':False},{'identity_error':True},
                       {'model':'different-model'}):
            with self.subTest(change=change):
                old,current=self.fixture()
                current['astra'].update(change)
                self.assertIn(self.ident,gate.historical_obligations([(5,old)],current))

    def test_new_peer_objection_is_preserved_even_if_origin_resolves(self):
        old,current=self.fixture()
        current['fable']['review']['prior_findings']=[{'id':self.ident,'resolution':'unresolved',
            'reason':'A new counterexample, different from the earlier copy.'}]
        self.assertIn(self.ident,gate.historical_obligations([(5,old)],current))
        gate.carry_obligations(current,[(5,old)])
        self.assertIn(self.ident,gate.override_findings(current,HEAD))

    def test_later_reopening_cannot_be_erased_by_replaying_old_resolution(self):
        old,current=self.fixture()
        later={'fable':envelope('fable',run='3',complete=False,review=report(decision='changes_requested',
            prior_findings=[{'id':self.ident,'resolution':'unresolved','reason':'Later counterexample.'}]))}
        self.assertIn(self.ident,gate.historical_obligations([(5,old),(6,current),(7,later)],copy.deepcopy(current)))


class ReviewRoundOneRegressions(unittest.TestCase):
    def test_access_reference_follows_its_finding_when_ids_swap(self):
        identity={'run':'7','attempt':'1','reviewer':'astra'}
        first=report(report='Short',decision='changes_requested',findings=[
            {'id':'F1','kind':'error','objection':'A substantive denominator error.'},
            {'id':'F2','kind':'source_access','objection':'The cited source could not be opened.'}],
            source_checks=[{'source_id':'S','location':'Theorem 1','outcome':'unavailable',
                           'detail':'The external source is unavailable to this reviewer.'}],
            access_limitations=[{'finding_id':'F2','source_ids':['S'],
                                 'detail':'Only access to the cited source is missing.'}])
        second=copy.deepcopy(first);second['report']=report()['report']
        second['findings'][0]['id']='F2';second['findings'][1]['id']='F1'
        second['access_limitations'][0]['finding_id']='F1'
        aliases=gate.delivered_finding_aliases([first,second],identity)
        normalized=gate.normalize_delivered_finding_ids(second,aliases,identity)
        gate.validate_review(normalized,set(),{})
        self.assertEqual(normalized['access_limitations'][0]['finding_id'],'F2')
        pair={'astra':envelope(run='7',review=normalized),
              'fable':envelope('fable',run='7',review=report(source_checks=[{
                  'source_id':'S','location':'Theorem 1','outcome':'verified',
                  'detail':'Read the printed source and its application without objection.'}]))}
        self.assertEqual([x['finding'] for x in gate.qualified_access_findings(pair)],['7-1-astra-F2'])
        with self.assertRaisesRegex(ValueError,'Uncovered findings: 7-1-astra-F1'):
            gate.overridden_decision(pair,{'7-1-astra-F2':{'reason':'Owner accepted access only'}},HEAD)

    def test_invented_scope_id_rejects_entire_multi_item_override(self):
        gh,app,event=MultiItemOverrides().setup_case(ids=[
            '1-1-astra-F1','1-1-astra-F2','scope-999999-1-fable'])
        provider=Mock(side_effect=AssertionError('No model call for override'))
        with patch.object(gate,'model_turn',side_effect=AssertionError('No provider request')):
            _,app,errors,state=run_pipeline(gh,app,event=event,provider=provider)
        provider.assert_not_called()
        self.assertTrue(errors)
        self.assertEqual(app.final['conclusion'],'failure')
        self.assertFalse(state.get('overrides'))
        self.assertTrue(any('scope-999999-1-fable' in p.get('body','')
            and p['body'].startswith('This override was ignored.') for p in gh.posts))


    def test_swapped_access_reference_survives_both_provider_delivery_paths(self):
        for family in gate.MODELS:
            with self.subTest(family=family):
                first=report(report='Short',decision='changes_requested',findings=[
                    {'id':'F1','kind':'error','objection':'A denominator can vanish.'},
                    {'id':'F2','kind':'source_access','objection':'The source is unavailable.'}],
                    source_checks=[{'source_id':'S','location':'Theorem 1','outcome':'unavailable',
                                    'detail':'The source could not be opened.'}],
                    access_limitations=[{'finding_id':'F2','source_ids':['S'],'detail':'Only source access is missing; no mathematical objection.'}])
                second=copy.deepcopy(first);second['report']=report()['report']
                second['findings'][0]['id']='F2';second['findings'][1]['id']='F1'
                second['access_limitations'][0]['finding_id']='F1'
                (_,app,_,state),_,count,_=delivery_fixtures.DeliveredClosure().fixture(family,
                    response(family,[first],'one'),[response(family,[second],'two')])
                self.assertEqual(count,2)
                self.assertTrue(state['reports'][family]['complete'])
                value=state['reports'][family]['review']
                self.assertEqual(value['access_limitations'][0]['finding_id'],'F2')
                self.assertEqual(value['findings'][0]['kind'],'error')
                self.assertEqual(value['findings'][0]['id'],'F1')
                self.assertEqual(app.final['conclusion'],'failure')
                self.assertEqual(second['access_limitations'][0]['finding_id'],'F1')

    def test_full_local_and_reworded_access_ids_follow_the_current_content(self):
        identity={'run':'7','attempt':'1','reviewer':'astra'}
        old=report(findings=[{'id':'F1','kind':'source_access','objection':'Earlier source access.'}])
        for raw,ref in [('F1','F1'),('7-1-astra-F1','F1'),('F1','7-1-astra-F1'),
                        ('7-1-astra-F1','7-1-astra-F1')]:
            with self.subTest(raw=raw,ref=ref):
                value=report(decision='changes_requested',findings=[{
                    'id':raw,'kind':'source_access','objection':'A different source is unavailable.'}],
                    source_checks=[{'source_id':'S','location':'T1','outcome':'unavailable','detail':'This precise source could not be opened by the reviewer.'}],
                    access_limitations=[{'finding_id':ref,'source_ids':['S'],'detail':'Only source access is missing; no mathematical objection.'}])
                aliases=gate.delivered_finding_aliases([old,value],identity)
                normalized=gate.normalize_delivered_finding_ids(value,aliases,identity)
                self.assertEqual(normalized['access_limitations'][0]['finding_id'],normalized['findings'][0]['id'])
                self.assertNotEqual(normalized['findings'][0]['id'],'F1')
                gate.validate_review(normalized,set(),{})

    def test_ambiguous_access_reference_rejected_without_losing_objections(self):
        identity={'run':'7','attempt':'1','reviewer':'astra'}
        value=report(findings=[{'id':'F1','objection':'First substantive error.'},
                              {'id':'F1','objection':'Second substantive error.'}],
                     access_limitations=[{'finding_id':'F1','source_ids':['S'],'detail':'Ambiguous.'}])
        aliases=gate.delivered_finding_aliases([value],identity)
        with self.assertRaisesRegex(ValueError,'ambiguous access finding reference'):
            gate.normalize_delivered_finding_ids(value,aliases,identity)
        saved=gate.delivered_obligations([value],identity,{})
        self.assertEqual(len(saved['findings']),2)
        self.assertIn('First substantive error',str(saved))
        self.assertIn('Second substantive error',str(saved))

    def test_prior_access_reference_stays_bound_to_the_known_pending_item(self):
        identity={'run':'7','attempt':'1','reviewer':'astra'}
        first=report(findings=[{'id':'F1','objection':'First objection.'}])
        second=report(findings=[{'id':'F1','objection':'Different objection.'}],
            prior_findings=[{'id':'7-1-astra-F1','resolution':'unresolved','reason':'Still open.'}],
            access_limitations=[{'finding_id':'7-1-astra-F1','source_ids':['S'],'detail':'Prior source.'}])
        aliases=gate.delivered_finding_aliases([first,second],identity)
        with self.assertRaisesRegex(ValueError,'Ambiguous prior finding reference'):
            gate.normalize_delivered_finding_ids(second,aliases,identity)
        # Both a fresh reused ID and an old full ID in this payload are ambiguous.
        with self.assertRaisesRegex(ValueError,'ambiguous access finding reference'):
            gate.normalize_delivered_finding_ids(second,aliases,identity,{'7-1-astra-F1'})
        second['findings']=[]
        value=gate.normalize_delivered_finding_ids(second,aliases,identity,{'7-1-astra-F1'})
        self.assertEqual(value['prior_findings'][0]['id'],'7-1-astra-F1')
        self.assertEqual(value['access_limitations'][0]['finding_id'],'7-1-astra-F1')

    def test_real_app_only_scope_is_overridable_without_a_report_comment(self):
        gh,app,event=MultiItemOverrides().setup_case(ids=['1-1-astra-F1','1-1-astra-F2','scope-1-1-fable'])
        pair=json.loads(app.checks[5]['output']['text'])['reports']
        pair['fable']['review']=report(decision='changes_requested',scope_complete=False,
                                      not_reviewed=['One source remains unread.'])
        app.prior(pair)
        gh.comments=[event['comment']]
        provider=Mock(side_effect=AssertionError('No model for an override'))
        with patch.object(gate,'model_turn',side_effect=AssertionError('No provider request')):
            _,app,errors,state=run_pipeline(gh,app,event=event,provider=provider)
        provider.assert_not_called()
        self.assertEqual(errors,[])
        self.assertEqual(app.final['conclusion'],'success')
        self.assertEqual(set(state['overrides']),{'1-1-astra-F1','1-1-astra-F2','scope-1-1-fable'})

    def test_scope_from_a_report_comment_without_app_record_is_not_recognized(self):
        gh,app,event=MultiItemOverrides().setup_case(ids=['1-1-astra-F1','1-1-astra-F2','scope-999999-1-fable'])
        gh.comments.insert(0,report_comment(envelope('fable',run='999999',review=report(
            decision='changes_requested',scope_complete=False,not_reviewed=['Not in an App record.']))))
        provider=Mock(side_effect=AssertionError('No model for an override'))
        with patch.object(gate,'model_turn',side_effect=AssertionError('No provider request')):
            _,app,errors,state=run_pipeline(gh,app,event=event,provider=provider)
        provider.assert_not_called()
        self.assertTrue(errors)
        self.assertEqual(app.final['conclusion'],'failure')
        self.assertFalse(state.get('overrides'))


if __name__=='__main__':
    unittest.main()
