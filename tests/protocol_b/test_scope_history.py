import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch
from test_gate import gate, FakeGH, FakeApp, HEAD, BASE, APP_ID, report, envelope, comment, run_pipeline


class ScopeHistory(unittest.TestCase):
    def earlier(self, head='c'*40):
        gh, app = FakeGH(), FakeApp()
        pair = {'astra': envelope(head=head, review=report(decision='changes_requested', findings=[
            {'id': 'F1', 'location': 'p:1', 'objection': 'An earlier counterexample remains.'}])),
            'fable': envelope('fable', head=head)}
        app.prior(pair, ident=1)
        app.checks[1]['head_sha'] = head
        value=json.loads(app.checks[1]['output']['text'])
        value.update(head=head,review_round={'number':1,'run':'1','attempt':'1','started':True,'trigger':'automatic'})
        app.checks[1]['output']['text']=json.dumps(value)
        gh.comments=[comment(gate.ROUND_MARKER+'\n```json\n'+json.dumps({'check':1})+'\n```')]
        gh.author_permission='read'
        return gh, app

    def test_new_head_absent_review_preserves_old_finding_and_scope_only_override_fails(self):
        gh, app=self.earlier()
        with patch.object(gate,'model_turn',side_effect=AssertionError('No provider')):
            _, app, _, state=run_pipeline(gh,app,provider=Mock(side_effect=AssertionError('No review')))
        saved=json.loads(app.final['output']['text'])['reports']
        self.assertIn('1-1-astra-F1',saved['astra']['carried_findings'])
        scopes={i['id']:{} for i in state['scope_items']}
        with self.assertRaisesRegex(ValueError,'1-1-astra-F1'):
            gate.overridden_decision(saved,scopes,HEAD)
        next_gh,next_app=self.earlier()
        next_gh.permission='admin'
        next_app.prior(saved,ident=5)
        next_gh.comments += [comment('/protocol-b override '+HEAD+' '+ident+' Explicit scope decision','collaborator') for ident in scopes]
        event={'issue':{'number':1},'comment':next_gh.comments[-1],'sender':{'login':'collaborator'}}
        with patch.object(gate,'model_turn',side_effect=AssertionError('No provider')):
            _,app,_,state=run_pipeline(next_gh,next_app,event=event,provider=Mock(side_effect=AssertionError('No review')))
        self.assertEqual(app.final['conclusion'],'failure')
        self.assertIn('1-1-astra-F1',state['summary'])
        self.assertFalse(next_gh.merge_requests)

    def test_comment_only_rejection_survives_empty_app_and_requires_its_own_decision(self):
        gh,app=self.earlier()
        old=json.loads(app.checks[1]['output']['text'])['reports']['astra']
        gh.comments.append(comment(gate.MARKER+'\n```json\n'+json.dumps(old)+'\n```'))
        payload=json.loads(app.checks[1]['output']['text']);payload['reports']={}
        app.checks[1]['output']['text']=json.dumps(payload)
        _,app,_,state=run_pipeline(gh,app,provider=Mock(side_effect=AssertionError('No review')))
        item=state['reports']['astra']['carried_findings']['1-1-astra-F1']
        self.assertEqual(item['origin_reviewer'],'history')
        self.assertIn('not authenticated model identity',item['reason'])
        self.assertIn('sha256',item['report_comment'])
        scopes={i['id']:{} for i in state['scope_items']}
        with self.assertRaisesRegex(ValueError,'1-1-astra-F1'):
            gate.overridden_decision(state['reports'],scopes,HEAD)
        self.assertIn('1-1-astra-F1',gate.overridden_decision(state['reports'],{**scopes,'1-1-astra-F1':{}},HEAD))

    def test_empty_intervening_app_record_does_not_mask_same_head_rejection(self):
        gh, app=self.earlier(HEAD)
        app.checks[2]=copy.deepcopy(app.checks[1]);app.checks[2]['id']=2
        value=json.loads(app.checks[2]['output']['text']);value['reports']={}
        app.checks[2]['output']['text']=json.dumps(value)
        _,app,_,state=run_pipeline(gh,app,event={'inputs':{'pull_request':'1'}},provider=Mock(side_effect=AssertionError('No review')))
        self.assertEqual(state['reports']['astra']['review']['findings'][0]['id'],'F1')
        with self.assertRaisesRegex(ValueError,'1-1-astra-F1'):
            gate.overridden_decision(state['reports'],{},HEAD)

    def test_comment_failure_keeps_completed_rejection_in_authoritative_state(self):
        gh=FakeGH();original=gh.call;failed=[]
        def call(path,method='GET',data=None):
            if method=='POST' and path.endswith('/comments') and data['body'].startswith(gate.MARKER) and not failed:
                failed.append(True)
                saved=json.loads((gate.OUT/'decision.json').read_text(encoding='utf-8'))
                family=json.loads(data['body'].split('```json\n')[1].split('\n```')[0])['reviewer']
                self.assertEqual(saved['reports'][family]['review']['findings'][0]['id'],'F1')
                raise RuntimeError('One-shot comment failure')
            return original(path,method,data)
        gh.call=call
        def provider(reviewer):
            reviewer.history_read=True;reviewer.reads=[{'path':'p.tex','revision':HEAD,'start':1,'count':1}]
            return report(decision='changes_requested',findings=[{'id':'F1','location':'p:1','objection':'Counterexample.'}])
        _,app,_,state=run_pipeline(gh,provider=provider)
        self.assertTrue(failed)
        for family in gate.MODELS:
            self.assertTrue(state['reports'][family]['complete'])
            self.assertEqual(state['reports'][family]['review']['findings'][0]['id'],'F1')
        self.assertEqual(app.final['conclusion'],'failure')
        with self.assertRaisesRegex(ValueError,'F1'):
            gate.overridden_decision(state['reports'],{'scope-7-1-astra':{},'scope-7-1-fable':{}},HEAD)

    def test_working_comment_failure_with_text_and_finish_preserves_delivered_finding(self):
        gh=FakeGH();original=gh.call;failed=[];actual_run=gate.Review.run
        def call(path,method='GET',data=None):
            if method=='POST' and path.endswith('/comments') and data['body'].startswith(gate.WORKING_MARKER) and not failed:
                failed.append(True);raise RuntimeError('One-shot working-comment failure')
            return original(path,method,data)
        gh.call=call
        def provider(reviewer):
            reviewer.history_read=True;reviewer.reads=[{'path':'p.tex','revision':HEAD,'start':1,'count':1}]
            return actual_run(reviewer) if reviewer.family=='fable' else report()
        value=report(decision='changes_requested',findings=[{'id':'F1','objection':'Delivered counterexample'}])
        response=([{'type':'text','text':'I found a counterexample.'},
                   {'type':'tool_use','id':'finish','name':'finish_review','input':value}],
                  gate.MODELS['fable'],{},'one','end_turn')
        with patch.object(gate,'model_turn',return_value=response):
            _,app,_,state=run_pipeline(gh,provider=provider)
        self.assertTrue(failed)
        self.assertTrue(state['reports']['fable']['complete'])
        self.assertEqual(state['reports']['fable']['review']['findings'][0]['id'],'F1')
        self.assertEqual(app.final['conclusion'],'failure')
        with self.assertRaisesRegex(ValueError,'7-1-fable-F1'):
            gate.overridden_decision(state['reports'],{'scope-7-1-fable':{}},HEAD)

    def test_invalid_finish_gets_correction_turn_without_dropping_objection(self):
        gh=FakeGH();review=gate.Review(gh,gh.pr,[],[],{},{},'trusted','fable','local mathematical')
        review.history_read=True;review.reads=[{'path':'p.tex','revision':HEAD,'start':1,'count':1}]
        invalid=report(decision='changes_requested',findings=[{'id':'F1','kind':'gap','attempted_resolution':'',
            'objection':'The exceptional case lacks a proof.'}])
        corrected=copy.deepcopy(invalid)
        corrected['findings'][0]['attempted_resolution']='Checked the preceding lemma; its positivity hypothesis excludes this exceptional zero case.'
        def response(value,ident):
            return ([{'type':'tool_use','id':ident,'name':'finish_review','input':value}],gate.MODELS['fable'],{},ident,'end_turn')
        with tempfile.TemporaryDirectory() as tmp,patch.object(gate,'OUT',Path(tmp)),patch.object(gate,'model_turn',side_effect=[response(invalid,'one'),response(corrected,'two')]) as model:
            result=review.run()
            self.assertEqual(result['findings'][0]['id'],'F1')
            self.assertEqual(model.call_count,2)
            self.assertIn('Correct the form',str(model.call_args.args[2]))
            self.assertTrue((Path(tmp)/'fable-delivered-final.json').exists())

    def test_interrupted_correction_retains_delivered_substantive_finding(self):
        def provider(reviewer):
            reviewer.invalid_finish=report(decision='changes_requested',findings=[{'id':'F1','kind':'gap',
                'attempted_resolution':'','objection':'A delivered gap, before the provider failed.'}])
            raise RuntimeError('Provider failed during correction')
        _,app,_,state=run_pipeline(provider=provider)
        self.assertEqual(app.final['conclusion'],'failure')
        for r in state['reports'].values():
            self.assertEqual(r['review']['findings'][0]['id'],'F1')
            self.assertIn('Delivered final report',r['review']['report'])
        scopes={i['id']:{} for i in state['scope_items']}
        with self.assertRaisesRegex(ValueError,'F1'):
            gate.overridden_decision(state['reports'],scopes,HEAD)

    def test_absent_runtime_records_do_not_count_as_paid_legacy_rounds(self):
        gh=FakeGH();gh.author_permission='read'
        _,app,_,_=run_pipeline(gh,provider=Mock(side_effect=AssertionError('No review')))
        _,_,_,state=run_pipeline(gh,app,provider=Mock(side_effect=AssertionError('No review')))
        self.assertEqual(state['automatic_rounds'],0)

    def test_carried_metadata_cannot_revive_an_actual_resolution(self):
        carried={'1-1-astra-F1':{'origin_reviewer':'astra','resolution':'unresolved','reason':'Old gap'}}
        resolved=envelope(run='2',review=report(prior_findings=[{'id':'1-1-astra-F1','resolution':'resolved','reason':'Proof inserted'}]))
        absent=envelope('fable',complete=False,carried_findings=carried)
        self.assertEqual(gate.historical_obligations([(1,{'fable':absent})],{'astra':resolved,'fable':absent}),{})

    def test_admin_can_address_an_app_finding_whose_comment_was_not_delivered(self):
        gh,app=FakeGH(),FakeApp();gh.permission='admin'
        pair={'astra':envelope(review=report(decision='changes_requested',findings=[{'id':'F1','objection':'Counterexample'}])), 'fable':envelope('fable')}
        app.prior(pair)
        command=comment('/protocol-b override '+HEAD+' 1-1-astra-F1 Explicit decision on App record','collaborator')
        gh.comments=[command]
        event={'issue':{'number':1},'comment':command,'sender':{'login':'collaborator'}}
        with patch.object(gate,'model_turn',side_effect=AssertionError('No provider')):
            _,app,errors,state=run_pipeline(gh,app,event=event,provider=Mock(side_effect=AssertionError('No review')))
        self.assertEqual(errors,[])
        self.assertEqual(app.final['conclusion'],'success')
        self.assertIn('1-1-astra-F1',state['overrides'])

    def test_actual_resolutions_retire_carried_obligations(self):
        earlier={'astra':envelope(review=report(decision='changes_requested',findings=[{'id':'F1','objection':'Gap'}]))}
        current={'astra':envelope(run='2',review=report(prior_findings=[{'id':'1-1-astra-F1','resolution':'resolved','reason':'Proof inserted at p:1.'}]))}
        self.assertEqual(gate.historical_obligations([(1,earlier)],current),{})


if __name__=='__main__':
    unittest.main()
