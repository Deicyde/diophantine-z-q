#!/usr/bin/env python3
"""Check the exact main-integration delta, then run the unchanged historical gate.

Only README.md and this workflow's historical identities are resolved through
fixed archival bytes. All mathematical and review inputs remain live reads.
"""
from pathlib import Path
import argparse,copy,hashlib,importlib.util,json,resource
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
AUTHORS=('/root/d214_sol_closure_ledger','/root/pr30_integration_author_recovery')
README='README.md'
WORKFLOW='.github/workflows/quartic214-manuscript.yml'
CHECKER='research/quartic214-manuscript-review/check_records.py'
MANIFEST='research/quartic214-manuscript/RELEASE_MANIFEST.json'
DECISION='research/quartic214-manuscript-review/REVIEW_DECISION.json'
AUTHORITY={CHECKER:'d7cbb73da766903e3b1419e5c9501e69ce9c36f51666597ace5240da3a3bea9c',MANIFEST:'f0aa633ae5e88aa49a5966bcd6152663b723cbef11925a0c76e5f9b77701f539',DECISION:'8eb7a8969ab80598b5841d07a67327a7d8552fca8c4ee5e73522d9d42d0ac3ab'}
ARCHIVES={README:('historical/README.md','761aa1e86ea71bdc9e9b8e6bd7b7318ee9e8d49f9d40c1496a66cd8e7cbd9dde'),WORKFLOW:('historical/quartic214-manuscript.yml','44213c08614752640e03167ac0a94bddca0a4a5d4527a5df587a54783eb32317')}
NOTE=(b'For the conditional Lean formalization, contribution targets and CI checks, see\n'
      b'the [Lean contribution guide](docs/lean-contributions.md). The root kernel project\n'
      b"and the manuscript's explicit quartic have distinct proof status.\n\n")
OLD_COMMAND=b'research/quartic214-manuscript-review/check_records.py --self-test --reviewed-artifacts'
NEW_COMMAND=b'research/quartic214-main-integration/check_historical_records.py --self-test --reviewed-artifacts'
PATH_ANCHOR=b"      - 'research/quartic214/**'\n"
NEW_TRIGGER=b"      - 'research/quartic214-main-integration/**'\n"
def sha(b):return hashlib.sha256(b).hexdigest()
def require(ok,reason):
 if not ok:raise ValueError(reason)
def safe(base,path):
 p=Path(path);require(not p.is_absolute()and'..'not in p.parts,'unsafe-path');return base/p
def frozen(data,expected):require(sha(data)==expected,'changed-frozen-evidence')
def exact_archives():
 out={}
 for key,(path,digest)in ARCHIVES.items():
  b=safe(HERE,path).read_bytes();frozen(b,digest);out[key]=b
 return out
def expected_readme(old):
 anchor=b'## Verification scope\n\n';require(old.count(anchor)==1,'ambiguous-historical-readme-anchor');return old.replace(anchor,anchor+NOTE,1)
def expected_workflow(old):
 require(old.count(OLD_COMMAND)==1 and old.count(PATH_ANCHOR)==1,'ambiguous-historical-workflow-anchor')
 return old.replace(OLD_COMMAND,NEW_COMMAND,1).replace(PATH_ANCHOR,PATH_ANCHOR+NEW_TRIGGER,1)
def check_current(archives,current):
 require(current[README]==expected_readme(archives[README]),'unexpected-current-readme-delta')
 require(current[WORKFLOW]==expected_workflow(archives[WORKFLOW]),'unexpected-current-workflow-delta')
def check_override_domain(overrides):require(set(overrides)==set(ARCHIVES),'undeclared-historical-substitution')
def check_record_binding(q):
 b=safe(ROOT,q['path']).read_bytes();require(sha(b)==q['sha256']and len(b)==q['bytes'],'stale-continuation-binding')
def check_continuation(q):
 require(q['schema']=='q214-main-integration-historical-continuation/v1','incorrect-continuation-schema')
 require(q['authors']==list(AUTHORS),'incorrect-continuation-authors')
 require(q['role']=='author historical-record continuation; no independent approval','incorrect-author-role')
 require(q['historical_substitutions']==sorted(ARCHIVES),'incorrect-substitution-scope')
 require(q['mathematical_acceptance_renewed']is False,'historical-wrapper-cannot-renew-mathematics')
 require(len({p['path']for p in q['bindings']})==len(q['bindings']),'duplicate-continuation-binding')
 for p in q['bindings']:check_record_binding(p)
 require({p['path']for p in q['bindings']}==set(AUTHORITY)|{README,WORKFLOW}|{'research/quartic214-main-integration/'+p for p,_ in ARCHIVES.values()}|{'research/quartic214-main-integration/check_historical_records.py','research/quartic214-main-integration/README.md'},'missing-continuation-binding')
 return q
def continuation_record():return check_continuation(json.loads((HERE/'CONTINUATION.json').read_text()))

def check_review_subjects(subjects,required):
 by={q['path']:q for q in subjects};require(len(by)==len(subjects),'duplicate-continuation-review-subject')
 require(required<=by.keys(),'missing-continuation-review-subject')
 for q in subjects:check_record_binding(q)
def check_reviewer_identity(receipt):
 require(receipt['author_tasks']==list(AUTHORS)and receipt['reviewer_task']not in AUTHORS,'self-approved-or-misattributed-continuation')
def check_receipt(receipt,record):
 require(receipt is not None,'missing-independent-continuation-review')
 require(receipt['schema']=='q214-historical-record-continuation-review/v1','incorrect-continuation-review-schema')
 require(receipt['decision']=='accepted-within-stated-scope','continuation-review-not-accepting')
 check_reviewer_identity(receipt)
 require(receipt['controller_eligibility_attested']is False,'unsupported-controller-claim')
 scope=receipt['scope'];require(scope['historical_substitutions']==sorted(ARCHIVES)and scope['all_other_bindings_current']is True and scope['readme_delta']=='exact-four-line-lean-guide-insertion'and scope['workflow_delta']=='wrapper-command-and-trigger-only'and scope['mathematical_acceptance_renewed']is False,'incorrect-continuation-review-scope')
 require(isinstance(receipt['limitations'],list)and receipt['limitations'],'missing-continuation-review-limit')
 required={q['path']for q in record['bindings']}|{'research/quartic214-main-integration/CONTINUATION.json'}
 check_review_subjects(receipt['subjects'],required)
def original_checker():
 for p,d in AUTHORITY.items():frozen(safe(ROOT,p).read_bytes(),d)
 spec=importlib.util.spec_from_file_location('frozen_q214_manuscript_review_gate',safe(ROOT,CHECKER));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def self_test(m,application,archives,current,record):
 out=[]
 def rejects(name,reason,fn):
  try:fn()
  except ValueError as e:require(str(e)==reason,'wrong-negative-control-reason:'+name+':'+str(e));out.append({'name':name,'rejected':True,'reason':reason})
  else:raise ValueError('negative-control-not-rejected:'+name)
 bad=dict(current);bad[README]+=b'\nNew arithmetic claim.\n';rejects('unexpected-readme-mathematics','unexpected-current-readme-delta',lambda:check_current(archives,bad))
 bad=dict(current);bad[README]=bad[README].replace(b'docs/lean-contributions.md',b'docs/other-guide.md');rejects('unexpected-readme-navigation','unexpected-current-readme-delta',lambda:check_current(archives,bad))
 bad=dict(current);bad[WORKFLOW]=bad[WORKFLOW].replace(b'          python -B scripts/check_audit_history.py --self-test\n',b'');rejects('removed-required-workflow-check','unexpected-current-workflow-delta',lambda:check_current(archives,bad))
 bad=dict(current);bad[WORKFLOW]+=b'\n      - run: true\n';rejects('unexpected-workflow-step','unexpected-current-workflow-delta',lambda:check_current(archives,bad))
 for key in ARCHIVES:
  rejects('altered-archive-'+('readme'if key==README else'workflow'),'changed-frozen-evidence',lambda k=key:frozen(archives[k]+b'\n',ARCHIVES[k][1]))
 bad=dict(archives);bad[application['manuscript']['path']]=b'not permitted';rejects('undeclared-override','undeclared-historical-substitution',lambda:check_override_domain(bad))
 p=application['manuscript']['path'];overrides=dict(archives);overrides[p]=safe(ROOT,p).read_bytes()+b'\n'
 rejects('changed-ordinary-current-proof','stale file binding: '+p,lambda:m.validate(application,overrides=overrides,release=True,decision_path=DECISION,manifest_path=MANIFEST))
 rejects('missing-independent-continuation-review','missing-independent-continuation-review',lambda:check_receipt(None,record))
 # A deliberately rejecting fixture is not an approval record.
 fixture={'schema':'q214-historical-record-continuation-review/v1','decision':'not-accepted'}
 rejects('nonaccepting-continuation-review','continuation-review-not-accepting',lambda:check_receipt(fixture,record))
 q={'path':README,'sha256':'0'*64,'bytes':len(current[README])};rejects('incorrect-current-review-binding','stale-continuation-binding',lambda:check_review_subjects([q],{README}))
 rejects('missing-review-subject','missing-continuation-review-subject',lambda:check_review_subjects([],{README}))
 for path in AUTHORITY:
  rejects('changed-original-authority-'+Path(path).name,'changed-frozen-evidence',lambda p=path:frozen(safe(ROOT,p).read_bytes()+b'\n',AUTHORITY[p]))
 # These identity-only fixtures cannot express or supply an acceptance decision.
 for author in AUTHORS:
  rejects('self-review-'+author.rsplit('/',1)[1],'self-approved-or-misattributed-continuation',lambda a=author:check_reviewer_identity({'author_tasks':list(AUTHORS),'reviewer_task':a}))
 rejects('omitted-recovery-author','self-approved-or-misattributed-continuation',lambda:check_reviewer_identity({'author_tasks':[AUTHORS[0]],'reviewer_task':'independent-fixture'}))
 good={'path':README,'sha256':sha(current[README]),'bytes':len(current[README])}
 rejects('duplicate-review-subject','duplicate-continuation-review-subject',lambda:check_review_subjects([good,good],{README}))
 bad=copy.deepcopy(record);bad['mathematical_acceptance_renewed']=True
 rejects('renewed-mathematical-acceptance','historical-wrapper-cannot-renew-mathematics',lambda:check_continuation(bad))
 bad=copy.deepcopy(record);bad['bindings'].pop()
 rejects('missing-continuation-binding','missing-continuation-binding',lambda:check_continuation(bad))
 bad=copy.deepcopy(record);bad['bindings'].append(bad['bindings'][0])
 rejects('duplicate-continuation-binding','duplicate-continuation-binding',lambda:check_continuation(bad))
 return out

def main():
 resource.setrlimit(resource.RLIMIT_AS,(512*1024*1024,512*1024*1024));p=argparse.ArgumentParser(description=__doc__);p.add_argument('--self-test',action='store_true');g=p.add_mutually_exclusive_group(required=True);g.add_argument('--reviewed-artifacts',action='store_true');g.add_argument('--author-check',action='store_true',help='Pre-review author execution only; cannot satisfy active reviewed-artifact workflow.');args=p.parse_args()
 archives=exact_archives();current={k:safe(ROOT,k).read_bytes()for k in ARCHIVES};check_current(archives,current);check_override_domain(archives);record=continuation_record();m=original_checker();application=json.loads((m.HERE/'ADAPTATION.json').read_text())
 if args.reviewed_artifacts:
  path=HERE/'REVIEW.json';check_receipt(json.loads(path.read_text())if path.is_file()else None,record)
 # The original validator receives only immutable historical identities for its
 # two explicitly superseded navigation/CI files. All other reads use ROOT.
 m.validate(application,overrides=archives,release=True,decision_path=DECISION,manifest_path=MANIFEST)
 old_controls=m.self_test(application)if args.self_test else[];controls=self_test(m,application,archives,current,record)if args.self_test else[]
 print(json.dumps({'status':'PASS','scope':'Exact four-line current README insertion and wrapper-only workflow continuation; unchanged original historical validator/manifest/scoped receipt checked with exactly two explicit historical identities, all other files current.','review_mode':'independently reviewed continuation'if args.reviewed_artifacts else'author pre-review check; no current independent continuation acceptance','historical_substitutions':sorted(archives),'original_negative_controls':old_controls,'integration_negative_controls':controls,'maximum_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'mathematical_acceptance_renewed':False,'controller_eligibility_attested':False},indent=2))
if __name__=='__main__':main()
