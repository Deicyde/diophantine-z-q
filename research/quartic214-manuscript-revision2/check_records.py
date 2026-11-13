#!/usr/bin/env python3
"""Bounded revision2 transformation/binding checks; no mathematical acceptance."""
from pathlib import Path
import argparse,copy,hashlib,importlib.util,json,resource
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
NINE={'source','constructed','domain','maps','object','normalization','local','exception','consumer'}
def sha(b):return hashlib.sha256(b).hexdigest()
def require(ok,msg):
 if not ok:raise ValueError(msg)
def safe(path):
 p=Path(path);require(not p.is_absolute()and'..'not in p.parts,'unsafe-path');return ROOT/p

def check_pin(q):
 b=safe(q['path']).read_bytes();require(sha(b)==q['sha256'],'stale-application-binding')
 if'bytes'in q:require(len(b)==q['bytes'],'stale-bound-size')
 if'lines'in q:
  a,z=q['lines'];require(1<=a<=z<=len(b.splitlines()),'invalid-passage-range');require(sha(b''.join(b.splitlines(keepends=True)[a-1:z]))==q['excerpt_sha256'],'stale-passage-binding')
def check_application(q):
 require({o['name']for o in q['obligations']}==NINE,'missing-obligation')
 for o in q['obligations']:require(o['required_input']and o['constructed_input_and_derivation'],'empty-connecting-obligation')
 check_pin(q['manuscript']);check_pin(q['old_manuscript']);check_pin(q['source_map']);check_pin(q['overlay']);check_pin(q['pdf']);check_pin(q['build'])
 for o in q.get('passages',[]):check_pin(o)
 for o in q.get('sources',[]):check_pin(o)
 for site in q.get('sites',[]):check_pin(site['source']);check_pin(site['receiving'])
 if'consuming_passage'in q:check_pin(q['consuming_passage'])
 if'source_application'in q:check_pin(q['source_application'])
 if'independent_finding_record'in q:check_pin(q['independent_finding_record'])
def check_repairs(tex,overlay):
 line=tex.splitlines()[2551]
 require(line.count(r'Z_{p}^{*}')==2 and line.count(r'(Z/rZ)^{*}')==2,'lost-unit-group-markers')
 require(r'R_{>0}'in line and r'R_{>}0'not in line,'lost-positive-real-index')
 require('least such modulus'in line and'primitive of conductor'in line,'missing-minimal-conductor')
 require(overlay['native_operative_note']in tex,'missing-operative-native-note')
 require(overlay['f7']['old_description']not in tex and'four quotient-quartic invariant checks'in tex and'all $36$ cross-ratio'in tex,'stale-catalogue-description')
def check_scoped_notation(tex):
 lines=tex.splitlines();norm=lambda n:''.join(lines[n-1].split())
 require(r"G_{F'}"in norm(2486)and all(r"G_{F'}"in norm(n)for n in [3575,3576,3578]),'lost-field-prime-scope')
 require(r'G_{\lceil t\rceil}'.replace(' ','')in norm(3539)and r'G_{\phi^{-1}(u)}'in norm(3540),'lost-evaluated-group-index')
 require(all(r'P^{1}_{R}'in norm(n)for n in [2655,2665])and r'P^{1}_{K}'in norm(2655)and r'P^{1}_{\kappa(x)}'in norm(2677)and r'P^{1}_{T}'in norm(2685)and r'\omega_{P^{1}_{R}/R}'in norm(2691)and r'A^{1}_{R}'in norm(2697),'lost-projective-index')
 require(all(t in norm(2918)for t in [r'\omega_{1}',r'\omega_{g}',r'dz_{1}',r'dz_{g}']),'lost-form-index')
 require(all(t in norm(2924)for t in [r'P^{1}_{t}',r'P_{1}',r'P_{d}',r'P_{j}'])and r'(\omega/dt(P_{j}))_{j}'in norm(2926)and r'P_{j}'in norm(2932),'lost-point-or-tuple-index')
 require(r'G_{Q_{p}}'in norm(2516)and r'Q_{p}^{*}'in norm(2516),'lost-local-field-index')
 require(r'b(ghg^{-1})=b(h)'in norm(2518),'lost-conjugation-inverse-scope')
 require(r'\circ'in norm(3073)and r'\circ'in norm(3571),'lost-composition-map')

def check_receipt(receipt,required):
 require(receipt['schema']=='quartic214-independent-receiving-review-v1','wrong-receiving-review-schema')
 require(receipt['reviewer_task']!=receipt['author_task']and receipt['author_task']=='/root/d214_sol_closure_ledger','self-approved-receiving-artifacts')
 require(receipt['decision']=='accepted-at-stated-scope','unaccepted-receiving-artifacts')
 require(receipt['controller_eligibility_attested']is False,'unsupported-controller-attestation')
 subjects={q['path']:q for q in receipt['subjects']};require(len(subjects)==len(receipt['subjects']),'duplicate-review-subject')
 require(required<=subjects.keys(),'missing-required-review-subject')
 for q in receipt['subjects']:check_pin(q)
 scope=receipt['scope'];require(scope['all_converted_semantic_transformations_reviewed']is True,'incomplete-receiving-semantic-review')
 for k,n in [('converted_proof_sources',19),('nonblank_converted_spans',789),('ir_rows',188),('ir_terms',1008),('coordinates',214),('retained_foundation_lines',39873),('retained_fragments',2)]:require(scope[k]==n,'incomplete-receiving-review-scope')
 require(bool(scope['selected_pdf_pages'])and bool(receipt['limitations']),'missing-receiving-review-boundary')

def check_source_map(mapping,tex):
 require(mapping['output_sha256']==sha(tex.encode()),'stale-source-map-output')
 require(sum(q['method']=='operative-current-native-primitive-source-application-note'for q in mapping['spans'])==1,'missing-operative-map-span')
 for path,q in mapping['sources'].items():
  require(sha(safe(path).read_bytes())==q['sha256'],'stale-bound-source')
 lines=tex.splitlines()
 for q in mapping['spans']:
  a,z=q['tex_lines'];require(1<=a<=z<=len(lines),'invalid-current-span')
  if q['method']=='exact-retained-body-LF':
   b=safe(q['source']).read_bytes().decode().splitlines();i,j=q['source_lines'];require('\n'.join(lines[a-1:z])=='\n'.join(b[i-1:j]),'changed-exact-foundation-body')
def check_build(d,tex):
 key='research/quartic214-manuscript-revision2/quartic214.tex';require(d['source_files'].get(key)==sha(tex.encode()),'stale-build-source-binding')
 check_pin(d['pdf']);require(d['limits']['parallel_tex_processes']==1 and d['limits']['child_address_space_bytes']<=1024**3 and not d['limits']['shell_escape'],'unsafe-build-record')
def check_manifest():
 p=HERE/'MANIFEST.json'
 if not p.exists():return
 d=json.loads(p.read_text());actual={str(p.relative_to(HERE))for p in HERE.rglob('*')if p.is_file()and p.name!='MANIFEST.json'}
 require(actual=={q['path']for q in d['files']},'missing-manifest-file')
 for q in d['files']:
  b=(HERE/q['path']).read_bytes();require(sha(b)==q['sha256']and len(b)==q['bytes'],'stale-manifest-file')
 for q in d['external_bindings']:check_pin(q)
def self_test(tex,overlay,mapping,app):
 out=[]
 def rejects(name,reason,fn):
  try:fn()
  except ValueError as e:require(str(e)==reason,'wrong-control-reason:'+name+':'+str(e));out.append({'name':name,'rejected':True,'reason':reason})
  else:raise ValueError('unrejected-control:'+name)
 rejects('lost-unit-group','lost-unit-group-markers',lambda:check_repairs(tex.replace(r'(Z/rZ)^{*}',r'(Z/rZ)',1),overlay))
 rejects('lost-positive-real-index','lost-positive-real-index',lambda:check_repairs(tex.replace(r'R_{>0}',r'R_{>}0',1),overlay))
 rejects('omitted-minimal-conductor','missing-minimal-conductor',lambda:check_repairs(tex.replace('least such modulus','a modulus',1),overlay))
 rejects('missing-operative-note','missing-operative-native-note',lambda:check_repairs(tex.replace(overlay['native_operative_note'],''),overlay))
 rejects('stale-catalogue','stale-catalogue-description',lambda:check_repairs(tex+'\n'+overlay['f7']['old_description'],overlay))
 q=copy.deepcopy(mapping);q['output_sha256']='0'*64;rejects('stale-mapped-output','stale-source-map-output',lambda:check_source_map(q,tex))
 q=copy.deepcopy(mapping);q['spans']=[p for p in q['spans']if p['method']!='operative-current-native-primitive-source-application-note'];rejects('missing-operative-span','missing-operative-map-span',lambda:check_source_map(q,tex))
 q=copy.deepcopy(app);q['manuscript']['sha256']='0'*64;rejects('stale-application','stale-application-binding',lambda:check_application(q))
 q=copy.deepcopy(app);q['obligations'].pop();rejects('missing-obligation','missing-obligation',lambda:check_application(q))
 q={'source_files':{'research/quartic214-manuscript-revision2/quartic214.tex':'0'*64}};rejects('stale-PDF-source','stale-build-source-binding',lambda:check_build(q,tex))
 def mutate_line(n,old,new):
  ls=tex.splitlines();require(old in ls[n-1],'invalid-negative-fixture');ls[n-1]=ls[n-1].replace(old,new,1);return'\n'.join(ls)+'\n'
 rejects('lost-field-prime','lost-field-prime-scope',lambda:check_scoped_notation(mutate_line(2486,r"G_{F'}",r"G_{F}'")))
 rejects('lost-group-index','lost-evaluated-group-index',lambda:check_scoped_notation(mutate_line(3539,r'G_{\lceil t\rceil}',r'G_{t}')))
 rejects('lost-projective-index','lost-projective-index',lambda:check_scoped_notation(mutate_line(2655,r'P^{1}_{R}',r'P1_{R}')))
 rejects('lost-form-index','lost-form-index',lambda:check_scoped_notation(mutate_line(2918,r'dz_{g}',r'\text{dzg}')))
 rejects('lost-conjugation','lost-conjugation-inverse-scope',lambda:check_scoped_notation(mutate_line(2518,'b(g h g^{-1})','b(\\text{ghg}^{-1})')))
 rejects('lost-composition','lost-composition-map',lambda:check_scoped_notation(mutate_line(3073,r'\circ','o')))
 return out
def main():
 resource.setrlimit(resource.RLIMIT_AS,(512*1024*1024,512*1024*1024));p=argparse.ArgumentParser();p.add_argument('--self-test',action='store_true');p.add_argument('--reviewed-artifacts',action='store_true',help='Require separate nonauthor receiving receipt with exact artifact subjects; does not attest controller eligibility.');p.add_argument('--allow-unbuilt',action='store_true',help='Source-only author hold; does not validate or accept any PDF.');a=p.parse_args()
 spec=importlib.util.spec_from_file_location('revision2_assembler',HERE/'assemble.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);expected,mapped=mod.assemble();raw=(HERE/'quartic214.tex').read_bytes();require(raw==expected,'stale-full-receiving-source');require((HERE/'SOURCE_SPANS.json').read_bytes()==mapped,'stale-full-source-map')
 tex=raw.decode();overlay=json.loads((HERE/'RECEIVING_OVERLAY.json').read_text());mapping=json.loads(mapped);check_repairs(tex,overlay);check_scoped_notation(tex);check_source_map(mapping,tex)
 apps=[json.loads((HERE/n).read_text())for n in ['ADAPTATION.json','F7_APPLICATION.json','F8_F11_APPLICATION.json']]
 for q in apps:check_application(q)
 if not a.allow_unbuilt:
  require((HERE/'BUILD.json').is_file()and(HERE/'quartic214.pdf').is_file(),'missing-matching-PDF-build');check_build(json.loads((HERE/'BUILD.json').read_text()),tex)
 check_manifest()
 if a.reviewed_artifacts:
  require(not a.allow_unbuilt,'reviewed-artifacts-requires-PDF-check')
  receipt_path=ROOT/'research/quartic214-protocol-d-review/RECEIVING_REVIEW.json';require(receipt_path.is_file(),'missing-independent-receiving-review')
  required={'research/quartic214-manuscript-revision2/'+n for n in ['quartic214.tex','quartic214.pdf','SOURCE_SPANS.json','RECEIVING_OVERLAY.json','ADAPTATION.json','F7_APPLICATION.json','F8_F11_APPLICATION.json','MANIFEST.json']}
  check_receipt(json.loads(receipt_path.read_text()),required)
 controls=self_test(tex,overlay,mapping,apps[0])if a.self_test else[]
 print(json.dumps({'status':'PASS','scope':'exact declared complete-receiving transformation, source/span/application/artifact byte bindings, explicit notation guards and intended-reason corruption controls; not mathematical validity, independent review, complete semantic coverage or ProtocolD acceptance','PDF_scope':'not checked; source-only author hold'if a.allow_unbuilt else'matching source/PDF/build byte binding checked','negative_controls':controls,'maximum_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'address_space_limit_bytes':512*1024*1024},indent=2))
if __name__=='__main__':main()
