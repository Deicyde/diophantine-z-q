#!/usr/bin/env python3
"""Bounded byte/record consistency checks. Does not decide mathematical validity."""
import argparse,copy,gzip,hashlib,io,json,resource,sys
from pathlib import Path
BASE=Path(__file__).resolve().parent
ROOT=BASE.parents[1]
MAX_FILE=64*1024*1024
REQUIRED_NATIVE={'.github/workflows/quartic214-protocol-d-progress.yml','manuscripts/quartic_v16.tex','research/version16/protocol/DOSSIER.json','research/version16/protocol/CONNECTIONS.json','research/version16/review/coverage/record-repair-001/REVIEW.md','research/version16/review/coverage/record-repair-001/REVIEW.json','research/version16/review/coverage/record-repair-001/PROTOCOL14-COVERAGE-REVIEW.json','research/version16/review/coverage/record-repair-001/ASSEMBLY-REVIEW.json','research/quartic214-manuscript/quartic214.tex','research/quartic214-manuscript/quartic214.pdf','research/quartic214/contracts/modularity-6.json','research/quartic214/contracts/INDEX.json','research/version16/protocol/record-repair-001/REPAIR.json'}
REQUIRED_EDGES={(s,c)for s in ['G2','G3']for c in ['M0','M2']}
REQUIRED_OBLIGATIONS={'source','constructed','domain','maps','object','normalization','local','exception','consumer'}
def sha(b):return hashlib.sha256(b).hexdigest()
def require(ok,msg):
 if not ok:raise ValueError(msg)
def safe(base,path):
 p=Path(path);require(not p.is_absolute()and'..'not in p.parts,'unsafe-relative-path');return base/p

def decode(entry,blob):
 require(len(blob)==entry['bytes']and sha(blob)==entry['sha256'],'stored-bytes-binding')
 if entry['compression']=='gzip-mtime0-no-name':
  require(blob[:3]==b'\x1f\x8b\x08'and blob[3]==0 and blob[4:8]==b'\0'*4,'malformed-compression-header')
  try:
   with gzip.GzipFile(fileobj=io.BytesIO(blob))as z:data=z.read(MAX_FILE+1)
  except(OSError,EOFError)as e:raise ValueError('malformed-compression-payload')from e
 elif entry['compression']=='none':data=blob
 else:raise ValueError('unknown-compression')
 require(len(data)<=MAX_FILE,'decompression-limit')
 require(len(data)==entry['uncompressed_bytes']and sha(data)==entry['uncompressed_sha256'],'logical-bytes-binding')
 return data

def check_external(manifest):
 by={e['path']:e for e in manifest['external_bindings']}
 require(len(by)==len(manifest['external_bindings']),'duplicate-external-binding')
 require(REQUIRED_NATIVE<=by.keys(),'missing-record-binding')
 idx=json.loads((ROOT/'research/quartic214/contracts/INDEX.json').read_text())
 require({q['path']for q in idx['contracts']}<=by.keys(),'missing-original-contract-binding')
 for name,q in by.items():
  if Path(name).is_absolute():continue  # external primary provenance is expressly not bundled
  p=safe(ROOT,name);require(p.is_file(),'missing-frozen-record');b=p.read_bytes();require(sha(b)==q['sha256']and len(b)==q['bytes'],'stale-proof-or-record')

def check_geometry(c):
 require({(q['supplier'],q['consumer'])for q in c['direct_edges']}==REQUIRED_EDGES,'missing-direct-edge')
 by={q['id']:q for q in c['passages']}
 require({'G2','G3','M0','M2','B-LINEAR','TEX-G2-G3','TEX-M0','TEX-M2','TEX-B-LINEAR'}<=by.keys(),'missing-consumer-passage')
 require({q['name']for q in c['obligations']}==REQUIRED_OBLIGATIONS,'missing-obligation')
 for q in c['obligations']:
  require(q['required_input']and q['constructed_input_and_derivation']and q['evidence_passage_ids'],'empty-obligation')
  require(set(q['evidence_passage_ids'])<=by.keys(),'missing-obligation-evidence')
 for q in list(by.values())+[c['original_contract'],c['manuscript'],c['pdf']]:
  b=safe(ROOT,q['path']).read_bytes();require(sha(b)==q['sha256']and len(b)==q['bytes'],'stale-geometry-proof')
  if'lines'in q:
   a,z=q['lines'];require(1<=a<=z<=len(b.splitlines()),'invalid-excerpt-range');require(sha(b''.join(b.splitlines(keepends=True)[a-1:z]))==q['excerpt_sha256'],'stale-geometry-excerpt')
 require(c['authors']and'acceptance'not in c,'author-cannot-supply-reviewer-acceptance')

def check_source_pin(q):
 b=safe(ROOT,q['path']).read_bytes();require(sha(b)==q['sha256'],'stale-reviewed-proof-or-contract')
 if'start_line'in q or'lines'in q:
  a,z=(q['start_line'],q['end_line'])if'start_line'in q else q['lines'];require(1<=a<=z<=len(b.splitlines()),'invalid-reviewed-excerpt')
  require(sha(b''.join(b.splitlines(keepends=True)[a-1:z]))==q['excerpt_sha256'],'stale-reviewed-excerpt')

def check_primitive(c):
 expected={('M3-EXTRACTION',p)for p in ['NATIVE-EXISTENCE','RECEIVING-NATIVE-EXISTENCE','RECEIVING-M3','H0-H2','RECEIVING-H0-H2']}
 require({(q['supplier'],q['consumer'])for q in c['direct_edges']}==expected,'missing-native-primitive-edge')
 passages={q['id']:q for q in c['passages']}
 require({x for edge in expected for x in edge}<=passages.keys(),'missing-native-primitive-passage')
 require({q['name']for q in c['obligations']}==REQUIRED_OBLIGATIONS,'missing-native-primitive-obligation')
 for q in c['obligations']:
  require(q['required_input']and q['constructed_input_and_connecting_derivation']and q['evidence_passage_ids'],'empty-native-primitive-obligation')
  require(set(q['evidence_passage_ids'])<=passages.keys(),'missing-native-primitive-evidence')
 for q in c['passages']+[c['manuscript'],c['pdf'],c['existing_contract'],c['source_metadata']]:check_source_pin(q)
 require(c['authors']and'acceptance'not in c,'author-cannot-supply-reviewer-acceptance')

def check_graph(links,uses,graph,coverage):
 use_ids=[q['id']for q in uses['uses']];section_ids=[q['section_id']for q in links['sections']]
 require(len(use_ids)==len(set(use_ids))and len(section_ids)==len(set(section_ids)),'duplicate-graph-node')
 require(len(links['sections'])==len(coverage['sections']),'missing-coverage-section')
 expected_section_edges=set()
 for actual,original in zip(links['sections'],coverage['sections']):
  require(all(actual.get(k)==v for k,v in original.items()),'changed-coverage-section')
  require(set(actual['source_use_ids'])<=set(use_ids),'missing-source-use')
  require(actual['source_use_ids']or(actual['classification']=='nonoperative_or_nonsubstantive'and actual['reason']),'unexplained-empty-source-use')
  expected_section_edges.update((u,actual['section_id'])for u in actual['source_use_ids'])
 require(expected_section_edges=={(e['from'],e['to'])for e in links['section_edges']},'missing-reviewed-section-edge')
 nodes=set(use_ids+section_ids)
 require(all(e['supplier']in nodes and e['consumer']in nodes for e in links['direct_application_edges']),'missing-direct-edge-node')
 require(graph['source_use_ids']==use_ids and graph['section_ids']==section_ids,'changed-declared-graph-nodes')
 require(graph['section_edges']==links['section_edges'],'missing-declared-section-edge')
 require(graph['direct_application_edges']==links['direct_application_edges'],'missing-declared-application-edge')

def check_review_files(prefix,items,logical):
 for q in items:
  name=prefix+q['path'];require(name in logical,'missing-review-record');b=logical[name];require(sha(b)==q['sha256']and len(b)==q['bytes'],'changed-verbatim-review-record')

def check_reviews(logical):
 for lane,manifest_name in [('rc','MANIFEST.json'),('analytic','REPORT_MANIFEST.json'),('geometry','MANIFEST.json'),('history-review','MANIFEST.json'),('closure-review','MATHEMATICAL_MANIFEST.json'),('closure-review','COVERAGE_LINK_MANIFEST.json')]:
  prefix='reviews/'+lane+'/'
  require(prefix+manifest_name in logical,'missing-review-manifest')
  m=json.loads(logical[prefix+manifest_name]);items=[dict(path=k,**v)for k,v in m.items()]if lane=='analytic'else m['files']
  check_review_files(prefix,items,logical)

def validate():
 m=json.loads((BASE/'EVIDENCE_MANIFEST.json').read_text());check_external(m);logical={}
 for e in m['entries']:
  require(e['logical_path']not in logical,'duplicate-logical-path');b=safe(BASE,e['path']).read_bytes();data=decode(e,b);logical[e['logical_path']]=data
  require(not e['logical_path'].lower().endswith(('.pdf','.png')),'unbundled-source-format')
  if e['logical_path'].lower().endswith('.txt'):require(e['logical_path']in {'inventory/PUBLIC-CORPUS-PATHS.txt','inventory/PUBLIC-INVENTORY-CANDIDATES.txt'},'unbundled-third-party-source-text')
 rc=json.loads(logical['reviews/rc/source-bindings.json'])
 external={e['path']:e for e in m['external_bindings']}
 for r in rc['whole_files']+rc['fresh_source_passages']+rc['receiving_passages']:
  require(r['path']in external and external[r['path']]['sha256']==r['sha256'],'missing-reviewed-source-binding');check_source_pin(r)
 for r in json.loads(logical['reviews/analytic/BINDINGS.json'])['files']:
  require(r['path']in external and external[r['path']]['sha256']==r['sha256'],'missing-reviewed-source-binding');check_source_pin(r)
 for r in json.loads(logical['reviews/geometry/REVIEWED_FILE_PINS.json']):
  require(r['path']in external and external[r['path']]['sha256']==r['sha256'],'missing-geometry-reviewed-source-binding');check_source_pin(r)
 idx=json.loads((ROOT/'research/quartic214/contracts/INDEX.json').read_text())
 for r in idx['contracts']:check_source_pin(r)
 for stem in ['M1','M3_M6']:
  binding=json.loads(logical['reviews/closure-review/'+stem+'_BINDINGS.json'])
  require(sha(logical['reviews/closure-review/'+stem+'_REVIEW.md'])==binding['report_sha256'],'stale-modularity-review-record')
  for r in binding['pins']:
   require(r['path']in external and external[r['path']]['sha256']==r['sha256'],'missing-modularity-reviewed-source-binding');check_source_pin(r)
 for name in ['SOURCE_PINS.json','READ_PASSAGES.json']:
  for r in json.loads(logical['reviews/history-review/'+name]):
   require(r['path']in external and external[r['path']]['sha256']==r['sha256'],'missing-history-reviewed-source-binding');check_source_pin(r)
 for r in json.loads(logical['reviews/closure-review/CURRENT_SECTION_COVERAGE.json'])['sections']+json.loads(logical['reviews/closure-review/FROZEN_ARTIFACT_IDENTITY.json']):
  require(r['path']in external and external[r['path']]['sha256']==r['sha256'],'missing-assembly-reviewed-source-binding');check_source_pin(r)
 reconciliation=json.loads(logical['reviews/closure-review/SOURCE_USE_RECONCILED.json'])
 require(reconciliation['initial_sha256']==sha(logical['reviews/closure-review/SOURCE_USE_INITIAL.json'])and reconciliation['assembly_report_sha256']==sha(logical['reviews/closure-review/ASSEMBLY_REVIEW.md']),'stale-source-reconstruction')
 prefix='reviews/closure-review/'
 links=json.loads(logical[prefix+'CURRENT_SECTION_USE_LINKS.json'])
 require(links['continued_from']['sha256']==sha(logical[prefix+'CURRENT_SECTION_COVERAGE.json'])and links['use_table']['sha256']==sha(logical[prefix+'SOURCE_USE_RECONCILED.json']),'stale-coverage-use-links')
 require(json.loads(logical[prefix+'COVERAGE_LINK_MANIFEST.json'])['prior_mathematical_manifest_sha256']==sha(logical[prefix+'MATHEMATICAL_MANIFEST.json']),'stale-coverage-continuation')
 graph=json.loads((BASE/'DECLARED_CURRENT_GRAPH.json').read_text())
 require(graph['reviewer_associations_sha256']==sha(logical[prefix+'CURRENT_SECTION_USE_LINKS.json'])and graph['use_table_sha256']==sha(logical[prefix+'SOURCE_USE_RECONCILED.json']),'stale-declared-graph')
 check_graph(links,reconciliation,graph,json.loads(logical[prefix+'CURRENT_SECTION_COVERAGE.json']))
 primitive=json.loads((BASE/'CURRENT_NATIVE_PRIMITIVE_APPLICATION.json').read_text());check_primitive(primitive)
 decision=json.loads(logical['reviews/closure-review/NATIVE_PRIMITIVE_REVIEW.json'])
 require(decision['contract']['sha256']==sha((BASE/'CURRENT_NATIVE_PRIMITIVE_APPLICATION.json').read_bytes()),'stale-native-primitive-review')
 require(decision['reviewer_task']not in primitive['authors'],'self-approved-native-primitive')
 history=json.loads(logical['reviews/history-review/NATIVE_PRIMITIVE_RESOLUTION.json'])
 require(history['contract_sha256']==decision['contract']['sha256']and history['review_sha256']==sha(logical['reviews/closure-review/NATIVE_PRIMITIVE_REVIEW.json']),'stale-history-primitive-resolution')
 check_reviews(logical);c=json.loads((BASE/'GEOMETRY_DIRECT_APPLICATION.json').read_text());check_geometry(c)
 if'reviews/geometry/DIRECT_EDGE_REVIEW.json'in logical:
  g=json.loads(logical['reviews/geometry/DIRECT_EDGE_REVIEW.json'])
  require(g['contract']['sha256']==sha((BASE/'GEOMETRY_DIRECT_APPLICATION.json').read_bytes()),'stale-independent-direct-edge-review')
  require(g['reviewer_task']not in c['authors'],'self-approved-direct-edge')
 require(c['finding_request']['path']in logical and sha(logical[c['finding_request']['path']])==c['finding_request']['original_sha256'],'missing-or-stale-finding-request')
 q=json.loads((BASE/'CURRENT_RECONCILIATION.json').read_text())
 require(q['geometry_direct_application']['sha256']==sha((BASE/'GEOMETRY_DIRECT_APPLICATION.json').read_bytes()),'stale-current-geometry-contract')
 require(q['native_primitive_application']['sha256']==decision['contract']['sha256']and q['native_primitive_application']['review_sha256']==sha(logical['reviews/closure-review/NATIVE_PRIMITIVE_REVIEW.json']),'stale-current-primitive-binding')
 require(q['source_level_assembly']['sha256']==sha(logical['reviews/closure-review/ASSEMBLY_REVIEW.md'])and q['source_level_coverage']['sha256']==sha(logical['reviews/closure-review/CURRENT_SECTION_USE_LINKS.json']),'stale-current-assembly-coverage-binding')
 require(q['full_protocol_d_closure']is False and q['current_pr30_protected_approval']is False,'unsupported-full-closure')
 if(BASE/'PACKET_MANIFEST.json').exists():
  p=json.loads((BASE/'PACKET_MANIFEST.json').read_text())
  actual={str(x.relative_to(BASE))for x in BASE.rglob('*')if x.is_file()and x.name!='PACKET_MANIFEST.json'}
  require(actual=={e['path']for e in p['files']},'incomplete-packet-file-manifest')
  for e in p['files']:
   b=safe(BASE,e['path']).read_bytes();require(sha(b)==e['sha256']and len(b)==e['bytes'],'stale-packet-file')
 return m,c

def self_test(m,c):
 results=[]
 def rejects(name,reason,fn):
  try:fn()
  except ValueError as e:
   require(str(e)==reason,'wrong-negative-control-reason:'+name+':'+str(e));results.append({'control':name,'rejected':True,'reason':str(e)})
  else:raise ValueError('negative-control-not-rejected:'+name)
 q=copy.deepcopy(m);q['external_bindings'][0]['sha256']='0'*64;rejects('stale-proof','stale-proof-or-record',lambda:check_external(q))
 q=copy.deepcopy(c);q['direct_edges'].pop();rejects('missing-direct-edge','missing-direct-edge',lambda:check_geometry(q))
 q=copy.deepcopy(c);q['passages']=[p for p in q['passages']if p['id']!='M2'];rejects('missing-consumer','missing-consumer-passage',lambda:check_geometry(q))
 q=copy.deepcopy(m);q['external_bindings']=[p for p in q['external_bindings']if p['path']!='research/version16/review/coverage/record-repair-001/REVIEW.json'];rejects('missing-native-record-binding','missing-record-binding',lambda:check_external(q))
 e=copy.deepcopy(next(e for e in m['entries']if e['compression'].startswith('gzip')));bad=b'\x1f\x8b\x08\x00'+b'\x00'*6+b'corrupt';e.update(bytes=len(bad),sha256=sha(bad));rejects('malformed-compression','malformed-compression-payload',lambda:decode(e,bad))
 e=copy.deepcopy(next(e for e in m['entries']if e['compression'].startswith('gzip')));e['uncompressed_sha256']='0'*64;rejects('changed-uncompressed-evidence','logical-bytes-binding',lambda:decode(e,safe(BASE,e['path']).read_bytes()))
 q=copy.deepcopy(c);q['obligations'].pop();rejects('missing-obligation','missing-obligation',lambda:check_geometry(q))
 q=copy.deepcopy(m);next(x for x in q['external_bindings']if x['path']=='research/version16/protocol/record-repair-001/REPAIR.json')['sha256']='0'*64;rejects('stale-declared-repair-record','stale-proof-or-record',lambda:check_external(q))
 q=copy.deepcopy(m);q['external_bindings']=[x for x in q['external_bindings']if x['path']!='research/quartic214/contracts/modularity-1.json'];rejects('missing-original-contract-record','missing-original-contract-binding',lambda:check_external(q))
 q={'path':'research/quartic214/proofs/uniform-existence.md','sha256':'0'*64};rejects('stale-reviewed-rc-analytic-source','stale-reviewed-proof-or-contract',lambda:check_source_pin(q))
 q=json.loads((BASE/'CURRENT_RECONCILIATION.json').read_text());q['geometry_direct_application']['sha256']='0'*64
 rejects('stale-current-geometry-binding','stale-current-geometry-contract',lambda:require(q['geometry_direct_application']['sha256']==sha((BASE/'GEOMETRY_DIRECT_APPLICATION.json').read_bytes()),'stale-current-geometry-contract'))
 q=copy.deepcopy(m);q['external_bindings'].append(q['external_bindings'][0]);rejects('duplicate-external-binding','duplicate-external-binding',lambda:check_external(q))
 p=json.loads((BASE/'CURRENT_NATIVE_PRIMITIVE_APPLICATION.json').read_text())
 q=copy.deepcopy(p);q['direct_edges'].pop();rejects('missing-native-primitive-edge','missing-native-primitive-edge',lambda:check_primitive(q))
 q=copy.deepcopy(p);q['obligations'].pop();rejects('missing-native-primitive-obligation','missing-native-primitive-obligation',lambda:check_primitive(q))
 q=copy.deepcopy(p);q['passages'][0]['excerpt_sha256']='0'*64;rejects('stale-native-primitive-excerpt','stale-reviewed-excerpt',lambda:check_primitive(q))
 q={'path':'research/quartic214/proofs/height-metric.md','sha256':'0'*64};rejects('stale-reviewed-height-proof','stale-reviewed-proof-or-contract',lambda:check_source_pin(q))
 prefix='reviews/closure-review/';manifest=json.loads((BASE/prefix/'MATHEMATICAL_MANIFEST.json').read_text())
 logical={prefix+q['path']:(BASE/prefix/q['path']).read_bytes()for q in manifest['files']}
 del logical[prefix+'ASSEMBLY_REVIEW.md']
 rejects('missing-mathematical-review','missing-review-record',lambda:check_review_files(prefix,manifest['files'],logical))
 def evidence(name):
  e=next(e for e in m['entries']if e['logical_path']==prefix+name)
  return json.loads(decode(e,safe(BASE,e['path']).read_bytes()))
 links=evidence('CURRENT_SECTION_USE_LINKS.json');uses=evidence('SOURCE_USE_RECONCILED.json');coverage=evidence('CURRENT_SECTION_COVERAGE.json');graph=json.loads((BASE/'DECLARED_CURRENT_GRAPH.json').read_text())
 for label,pair in [('named-theorem-edge',('U09','U10')),('section-only-edge',('U10','U13')),('unnamed-estimate-edge',('U17','U18'))]:
  q=copy.deepcopy(graph);q['direct_application_edges']=[e for e in q['direct_application_edges']if(e['supplier'],e['consumer'])!=pair]
  require(len(q['direct_application_edges'])==len(graph['direct_application_edges'])-1,'invalid-edge-control-fixture')
  rejects('missing-'+label,'missing-declared-application-edge',lambda:check_graph(links,uses,q,coverage))
 q=copy.deepcopy(uses);q['uses']=[u for u in q['uses']if u['id']!='U17']
 rejects('missing-coverage-source-use','missing-source-use',lambda:check_graph(links,q,graph,coverage))
 q=copy.deepcopy(graph);q['section_edges'].pop();rejects('missing-declared-section-edge','missing-declared-section-edge',lambda:check_graph(links,uses,q,coverage))
 q=copy.deepcopy(m);next(e for e in q['external_bindings']if e['path']=='research/quartic214/contracts/height-averaging.json')['sha256']='0'*64
 rejects('changed-supplier-contract-without-renewed-review','stale-proof-or-record',lambda:check_external(q))
 return results

def main():
 resource.setrlimit(resource.RLIMIT_AS,(512*1024*1024,512*1024*1024))
 p=argparse.ArgumentParser();p.add_argument('--self-test',action='store_true');a=p.parse_args()
 m,c=validate();controls=self_test(m,c)if a.self_test else[]
 print(json.dumps({'status':'PASS','scope':'artifact hashes, bounded deterministic gzip decoding, preserved reviewer-record bytes, frozen external files, direct edge/consumer/excerpt/obligation presence; not mathematical validity or approval','entries':len(m['entries']),'negative_controls':controls,'maximum_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'address_space_limit_bytes':512*1024*1024},indent=2))
if __name__=='__main__':main()
