import copy
import hashlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch
import urllib.request
import zipfile
from test_gate import gate, FakeGH, FakeApp, HEAD, BASE, changed, report, run_pipeline, workflow, envelope, comment, report_comment
from test_kernel_dispatch import KernelGH


class LeanProfile(unittest.TestCase):
    def fixture(self):
        gh=KernelGH()
        files=[changed('ZInQKernel/Example.lean')]
        contract=json.dumps({'files':{'ZInQKernel/Example.lean':'hash'}})
        run=gh.run()
        artifact={'id':55,'name':'kernel-audit','expired':False,'digest':'sha256:fixture',
                  'workflow_run':{'id':44,'head_sha':HEAD}}
        audit={'schema':'kernel-audit/v1','status':'passed','head_sha':HEAD,
               'contract_sha256':hashlib.sha256(contract.encode()).hexdigest(),
               'modules':['ZInQKernel.Example'],'allowed_axioms_used':['Classical.choice','propext','Quot.sound'],
               'runtime_declarations_not_replayed':['ZInQKernel.runtimeHelper'],
               'targets':[{'declaration':'Example','status':'open'}],
               'headline_type':'AssumptionH -> MainClaim'}
        return gh,files,run,artifact,audit

    def test_only_supported_lean_sources_and_build_configuration_qualify(self):
        for path in ['ZInQKernel.lean','ZInQKernel/Example.lean','lean/ZInQ/Contrib/X.lean',
                     'ThirdParty/GreenTao/Submission/Example.lean',
                     'lakefile.toml','lake-manifest.json','lean-toolchain','KERNEL_CONTRACT.json']:
            self.assertTrue(gate.lean_profile_eligible([changed(path)]),path)
        for path in ['README.md','manuscripts/x.tex','research/x.json','.github/workflows/kernel-lean.yml',
                     'scripts/audit_kernel.lean','ThirdParty/X.lean','Other.lean','lean/Frozen/BoundedIntegerPolynomial.lean']:
            self.assertFalse(gate.lean_profile_eligible([changed('ZInQKernel.lean'),changed(path)]),path)
        self.assertFalse(gate.lean_profile_eligible([]))
        self.assertFalse(gate.lean_profile_eligible([changed('ZInQKernel/X.lean',previous_filename='manuscripts/x.tex')]))

    def test_actual_axioms_conditional_types_and_runtime_exclusions_are_preserved(self):
        gh,files,run,artifact,audit=self.fixture()
        value=gate.validate_lean_audit(gh,gh.pr,files,run,artifact,audit)
        self.assertEqual(value['audit'],audit)
        self.assertEqual(value['audit']['targets'][0]['status'],'open')
        self.assertEqual(value['artifact'],55)

    def test_module_mapping_matches_all_existing_audited_roots(self):
        for path,module in [('ZInQKernel.lean','ZInQKernel'),('lean/ZInQ/Contrib/X.lean','ZInQ.Contrib.X'),
                            ('ThirdParty/GreenTao/Submission/X.lean','Submission.X')]:
            gh,files,run,artifact,audit=self.fixture()
            files=[changed(path)];audit['modules']=[module]
            self.assertEqual(gate.validate_lean_audit(gh,gh.pr,files,run,artifact,audit)['audit']['modules'],[module])

    def test_wrong_run_artifact_contract_and_uncovered_module_are_rejected(self):
        mutations=[('run','head_sha','d'*40),('run','conclusion','failure'),('run','path','fake.yml'),
                   ('run','repository',{'full_name':'other/repo'}),('artifact','expired',True),
                   ('artifact','workflow_run',{'id':45,'head_sha':HEAD}),('audit','contract_sha256','bad'),
                   ('audit','modules',[]),('audit','allowed_axioms_used',None)]
        for part,key,value in mutations:
            gh,files,run,artifact,audit=self.fixture()
            {'run':run,'artifact':artifact,'audit':audit}[part][key]=value
            with self.subTest(part=part,key=key),self.assertRaises(ValueError):
                gate.validate_lean_audit(gh,gh.pr,files,run,artifact,audit)

    def test_modified_auditor_cannot_supply_lean_profile_authority(self):
        gh,files,run,artifact,audit=self.fixture()
        gh.root_entries[HEAD]['scripts']['sha']='d'*40
        with self.assertRaisesRegex(ValueError,'helper inputs'):
            gate.validate_lean_audit(gh,gh.pr,files,run,artifact,audit)

    def test_pr_run_cannot_claim_exact_head_even_with_matching_audit_bytes(self):
        for associations in ([],[{'number':2,'base':{'sha':'e'*40}}]):
            gh,files,run,artifact,audit=self.fixture()
            run.update(event='pull_request',pull_requests=associations)
            with self.assertRaisesRegex(ValueError,'direct execution'):
                gate.validate_lean_audit(gh,gh.pr,files,run,artifact,audit)

    def test_no_test_merge_exception_even_when_a_diff_is_disjoint(self):
        gh,files,run,artifact,audit=self.fixture();audit['head_sha']='d'*40
        gh.comparison.update(files=[changed('docs/example.md')])
        with self.assertRaisesRegex(ValueError,'direct head'):
            gate.validate_lean_audit(gh,gh.pr,files,run,artifact,audit)

    def test_direct_run_without_pr_association_is_valid_for_a_fork(self):
        gh,files,run,artifact,audit=self.fixture()
        self.assertNotEqual(gh.pr['head']['repo']['full_name'],gh.repo)
        self.assertEqual(run['pull_requests'],[])
        self.assertEqual(gate.validate_lean_audit(gh,gh.pr,files,run,artifact,audit)['audited_head'],HEAD)

    def test_download_checks_digest_reads_only_json_and_strips_redirect_credentials(self):
        stream=io.BytesIO()
        with zipfile.ZipFile(stream,'w') as archive:
            archive.writestr('audit.json','{"status":"passed"}')
            archive.writestr('../../untrusted.py','raise Exception("never execute")')
        raw=stream.getvalue();gh=FakeGH();gh.headers={'Authorization':'Bearer fixture-secret'}
        artifact={'id':55,'size_in_bytes':len(raw),'digest':'sha256:'+hashlib.sha256(raw).hexdigest()}
        opener=Mock();opener.open.return_value=io.BytesIO(raw)
        with patch.object(urllib.request,'build_opener',return_value=opener) as build:
            self.assertEqual(gate.download_audit(gh,artifact),{'status':'passed'})
            redirect=build.call_args.args[0]
            request=urllib.request.Request('https://api.github.com/example',headers=gh.headers)
            target=redirect.redirect_request(request,None,302,'redirect',{},'https://storage.example/archive')
            self.assertFalse(target.has_header('Authorization'))
            with self.assertRaises(ValueError):redirect.redirect_request(request,None,302,'redirect',{},'http://storage.example/archive')
        artifact['digest']='sha256:wrong';opener.open.return_value=io.BytesIO(raw)
        with patch.object(urllib.request,'build_opener',return_value=opener),self.assertRaisesRegex(ValueError,'digest'):
            gate.download_audit(gh,artifact)

    def test_pending_or_failed_kernel_evidence_never_calls_models(self):
        gh=FakeGH();original=gh.pages
        gh.pages=lambda path:[changed('ZInQKernel/Example.lean')] if path.endswith('/files') else original(path)
        provider=Mock(side_effect=AssertionError('No review before audit'))
        with patch.object(gate,'model_turn',side_effect=AssertionError('No provider')):
            _,app,_,state=run_pipeline(gh,provider=provider)
        provider.assert_not_called()
        self.assertEqual(app.final['conclusion'],'action_required')
        self.assertIn('awaits exact-head kernel evidence',state['summary'])

    def test_ready_evidence_is_shown_to_both_reviewers(self):
        gh,files,run,artifact,audit=self.fixture();original=gh.pages
        gh.pages=lambda path:files if path.endswith('/files') else original(path)
        configure=gate.configure_budget;seen=[]
        evidence=gate.validate_lean_audit(gh,gh.pr,files,run,artifact,audit)
        def budget(files):
            gate.record('lean-preflight.json',{'ready':True,'head':HEAD,'base':BASE,'evidence':evidence})
            return configure(files)
        def provider(reviewer):
            seen.append(reviewer.input['lean_kernel_evidence'])
            self.assertIn('Do not re-prove the mathematical reasoning',reviewer.instructions)
            self.assertIn('EVERY changed Lean hunk',reviewer.instructions)
            self.assertIn('temporary',reviewer.instructions)
            return report()
        with patch.object(gate,'configure_budget',side_effect=budget):
            _,app,errors,state=run_pipeline(gh,provider=provider)
        self.assertEqual(errors,[])
        self.assertEqual(seen,[evidence,evidence])
        self.assertEqual(state['review_profile']['name'],'lean')
        self.assertEqual(app.final['conclusion'],'success')
        stored=json.loads(gate.decision_text(state,state['reports'],[]))
        provenance=stored['lean_kernel_provenance']
        self.assertEqual(provenance['run'],44)
        self.assertEqual(provenance['attempt'],1)
        self.assertEqual(provenance['artifact_digest'],'sha256:fixture')
        self.assertEqual(provenance['audited_head'],HEAD)
        self.assertNotIn('audit',provenance)
        self.assertEqual(provenance['audit_sha256'],hashlib.sha256(json.dumps(audit,sort_keys=True).encode()).hexdigest())
        self.assertIn('Temporary Option A',app.final['output']['summary'])

    def test_admin_scope_override_still_requires_authentic_kernel_evidence(self):
        for ready in (False,True):
            gh,files,run,artifact,audit=self.fixture();original=gh.pages
            gh.pages=lambda path:files if path.endswith('/files') else original(path)
            gh.permission='admin'
            app=FakeApp()
            pair={'astra':envelope(),'fable':envelope('fable',complete=False,review=report(scope_complete=False,not_reviewed=['Interrupted before inspection']))}
            app.prior(pair)
            item=gate.review_scope_item(pair['fable'])['id']
            command=comment('/protocol-b override '+HEAD+' '+item+' accept incomplete scope','collaborator')
            gh.comments=[report_comment(v) for v in pair.values()]+[command]
            event={'issue':{'number':1},'comment':command,'sender':{'login':'collaborator'}}
            evidence=gate.validate_lean_audit(gh,gh.pr,files,run,artifact,audit) if ready else None
            provider=Mock(side_effect=AssertionError('No model during override'))
            with self.subTest(ready=ready),patch.object(gate,'lean_evidence',return_value=evidence) as read,patch.object(gate,'ensure_kernel_dispatch',side_effect=AssertionError('No dispatch during override')):
                _,app,errors,state=run_pipeline(gh,app,provider=provider,event=event)
            provider.assert_not_called();read.assert_called_once()
            self.assertEqual(app.final['conclusion'],'success' if ready else 'action_required')
            if ready:
                self.assertEqual(errors,[])
                self.assertEqual(state['lean_evidence'],evidence)
            else:
                self.assertIn('awaits exact-head kernel evidence',state['summary'])

    def test_wait_runs_before_secret_exposure_and_preserves_candidate_code_isolation(self):
        preparation=workflow.split('  kernel_preflight:',1)[1].split('  run_reviewers:',1)[0]
        self.assertNotIn('secrets.',preparation)
        self.assertIn('PROGRAM_ACTION: wait-lean',preparation)
        self.assertNotIn('environment: protocol-b',preparation)
        self.assertNotIn('actions/checkout',workflow)
        self.assertNotIn('zipfile.extract',workflow)

    def test_wait_exits_on_changed_head_without_dispatch_or_provider_call(self):
        gh,files,_,_,_=self.fixture();original=gh.pages
        gh.pages=lambda path:files if path.endswith('/files') else original(path)
        def absent(*args):
            gh.pr['head']['sha']='d'*40
            return None
        with tempfile.TemporaryDirectory() as tmp:
            event=Path(tmp)/'event.json';event.write_text(json.dumps({'pull_request':{'number':1}}))
            with patch.dict(os.environ,{'MODE':'live','GITHUB_REF':'refs/heads/main','GITHUB_REPOSITORY':'x/y','GH_TOKEN':'fixture','GITHUB_EVENT_PATH':str(event)}),patch.object(gate,'OUT',Path(tmp)),patch.object(gate,'GitHub',return_value=gh),patch.object(gate,'lean_evidence',side_effect=absent),patch.object(gate.time,'sleep'),patch.object(gate,'model_turn',side_effect=AssertionError('No provider')):
                gate.wait_lean()
                state=json.loads((Path(tmp)/'lean-preflight.json').read_text())
        self.assertFalse(state['ready'])
        self.assertIn('changed',state['error'])
        self.assertFalse(gh.dispatches)

    def test_preflight_does_not_wait_when_inactive_wrong_test_pr_or_unauthorized(self):
        for mode,event in [('off',{'pull_request':{'number':1}}),
                           ('test',{'pull_request':{'number':2}}),
                           ('live',{'issue':{'number':1},'comment':{'body':'/protocol-b review',
                               'user':{'login':'reader','type':'User'}},'sender':{'login':'reader'}})]:
            gh,files,_,_,_=self.fixture();original=gh.pages
            gh.pages=lambda path:files if path.endswith('/files') else original(path)
            with tempfile.TemporaryDirectory() as tmp:
                event_path=Path(tmp)/'event.json';event_path.write_text(json.dumps(event))
                env={'MODE':mode,'TEST_PR':'1','GITHUB_REF':'refs/heads/main','GITHUB_REPOSITORY':'x/y',
                     'GH_TOKEN':'fixture','GITHUB_EVENT_PATH':str(event_path)}
                with patch.dict(os.environ,env),patch.object(gate,'OUT',Path(tmp)),patch.object(gate,'GitHub',return_value=gh),patch.object(gate,'lean_evidence') as evidence,patch.object(gate,'model_turn',side_effect=AssertionError('No provider')):
                    gate.wait_lean()
                    evidence.assert_not_called()
                    state=json.loads((Path(tmp)/'lean-preflight.json').read_text())
                    self.assertFalse(state['ready'])
            self.assertFalse(gh.dispatches)


if __name__=='__main__':
    unittest.main()
