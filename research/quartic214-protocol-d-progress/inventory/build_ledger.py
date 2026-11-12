from pathlib import Path
import json,hashlib,re,collections,functools
R=Path('/tmp/quartic214-manuscript-20261112');O=Path('/tmp/q214-d-next-20261112/inventory')
def read(p):return json.loads((R/p).read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
@functools.lru_cache(maxsize=None)
def bind(p):
 p=Path(p);a=p if p.is_absolute() else R/p
 return {'path':str(p),'sha256':sha(a.read_bytes()),'bytes':a.stat().st_size}
def save(n,d): (O/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
I=json.loads((O/'INITIAL-SOURCE-FIRST.json').read_text());D=read('research/version16/protocol/DOSSIER.json');C=read('research/version16/protocol/CONNECTIONS.json');S=read('research/quartic214-manuscript/SOURCE_SPANS.json');CI=read('research/quartic214/contracts/INDEX.json');T='manuscripts/quartic_v16.tex';M='research/quartic214-manuscript/quartic214.tex'
coverage={q['id']:q for q in D['coverage_index']}; uses={q['id']:q for q in D['reconciled_uses']}; connections={q['use_id']:q for q in C['connections']}
contracts=[]
for q in CI['contracts']:
 c=read(q['path']);contracts.append({'record':bind(q['path']),'application_id':c['application_id'],'manuscript':c.get('manuscript'),'proof':c.get('proof'),'construction_passages':c.get('construction_passages'),'application_passages':c.get('application_passages'),'consumer_passages':c.get('consumer_passages'),'status_as_reported':c.get('status'),'current_lane_status':'existing author contract located; no independent acceptance supplied'})
sp=[q for q in S['spans']if q.get('source')==T and q.get('source_lines')and q.get('tex_lines')]
rows=[]
for r in I['records']:
 w=dict(r);locations=[]
 if r['source']==T:locations=[(r['start'],r['end'])]
 else:
  for q in sp:
   a,b=q['tex_lines'];s,e=q['source_lines'];left=max(a,r['start']);right=min(b,r['end'])
   if left<=right and b-a==e-s:locations.append((s+left-a,s+right-a))
 cov=[]
 for q in D['coverage_index']:
  loc=q['location']
  if loc['pin']['path']==T and any(max(a,loc['start_line'])<=min(b,loc['end_line'])for a,b in locations):cov.append(q['id'])
 ids=sorted({u for c in cov for u in coverage[c]['use_ids']})
 w.update({'upstream_locations':locations,'candidate_existing_coverage_rows':cov,'candidate_existing_source_use_ids':ids,'candidate_existing_connection_ids':[u for u in ids if u in connections],'existing_evidence_status':'bound project proof and source-use/connecting records located'if ids else 'no matching imported row identified by mechanical range overlap; may be inline, front matter, catalog or new214 proof','historical_disposition':'unresolved at passage/application level in this author lane','current_incorporation':'text present in frozen manuscript; mathematical supplier-to-consumer match not independently accepted','review_action':'Read the complete passage; reconstruct exact required assertion and supplier; compare candidate matches; record or explicitly exclude all unnamed/section uses; obtain eligible nonauthor coverage decision.','mapping_limit':'Range overlap yields candidates only. It does not establish direct dependency or that an existing record covers this finer passage.'})
 if r['source']==M and not locations:
  srcs=sorted({q['source']for q in S['spans']if q.get('source')and q.get('tex_lines')and max(q['tex_lines'][0],r['start'])<=min(q['tex_lines'][1],r['end'])})
  w['source_span_inputs']=srcs;w['candidate_author_contracts']=[c['application_id']for c in contracts if any(p.get('path')in srcs for key in ['construction_passages','application_passages','consumer_passages']for p in c.get(key)or[])]
 rows.append(w)
save('PASSAGE-CLOSURE-LEDGER.json',{'role':'author preparation; not coverage acceptance','initial_freeze':bind(O/'INITIAL-SOURCE-FIRST.json'),'review_target':I['frozen_commit'],'complete_structural_line_partition':True,'semantic_source_use_reconstruction_complete':False,'unread_is_not_unproved':True,'records':rows})
U=[]
for u in D['reconciled_uses']:
 s=u.get('supplier')or{};c=connections.get(u['id']);U.append({'id':u['id'],'origin':bind('research/version16/protocol/DOSSIER.json'),'origin_pointer':'/reconciled_uses/'+str(len(U)),'consumer_claim':u.get('consumer'),'consumer_coverage_locations':[(p,coverage[p]['location'])for p in u.get('passages',[])if p in coverage],'prerequisite_statement':u.get('assertion'),'supplier':s,'publication_status_as_declared':s.get('publication'),'supplier_kind_as_declared':s.get('kind'),'existing_application_id':u.get('application_id'),'existing_inline_argument':u.get('inline_argument'),'connection_pointer':('/connections/'+str(C['connections'].index(c)))if c else None,'available_assertion_as_declared':c.get('available_assertion')if c else None,'connecting_derivation_as_declared':c.get('connecting_derivation')if c else None,'classification_as_declared':u.get('classification'),'classification_reason_as_declared':u.get('reason'),'historical_disposition':'unresolved here; exact older source-use and derivation located, not newly supplied or mathematically reclassified','incorporation':'supplier/consumer locators preserved; current214 composition still requires fresh dependency comparison','current_author_lane_status':'unread application; exact project record exists','needed_action':'Inspect actual source statements and connecting derivation; validate published edition/corrections and nine obligations; then eligible nonauthor decision or reuse decision at exact scope.'})
save('INHERITED-APPLICATION-QUEUE.json',{'role':'declared V16 records imported for reconciliation only; no new verdict','source_records':1190,'records':U})
H=[]
for f,key,idkey in [('research/version16/protocol/CONNECTIONS.json','findings','finding_id'),('docs/audit-history/issue2/register.json','items','number'),('research/version16/FINDINGS.json','findings','id'),('research/quartic214-manuscript-review/FINDINGS.json','findings','id'),('research/quartic214-manuscript-review/current-astra-20261112/FINDINGS.json','findings','id')]:
 d=read(f)
 for i,q in enumerate(d[key]):H.append({'id':str(q[idkey]),'origin':bind(f),'json_pointer':f'/{key}/{i}','recorded_finding':q,'author_lane_historical_disposition':'unresolved unless separately discussed in CORPUS-AND-ACTION-REPORT.md; old classification retained as evidence only','author_lane_incorporation':'not globally reclassified; source-consumer review required','needed_action':'Read original objection and actual earlier proposed proof, trace current consumed assertion, and obtain reviewed resolution/current binding. Preserve scope limitations and duplicate links.'})
save('HISTORICAL-FINDING-QUEUE.json',{'scope':'All entries in the five explicitly named public registers, not all objections ever received. PR30 complete fetched timeline separately retained. Original proof arguments for most entries unread here.','records':H})
# Whole-repository public path discovery only; no private sources followed.
paths=[]
for p in sorted(R.rglob('*')):
 if '.git'in p.parts or not p.is_file():continue
 rel=p.relative_to(R)
 if re.search(r'(audit|review|finding|source.use|source.inventory|application|coverage|objection|followup|register)',str(rel),re.I):paths.append(bind(rel))
save('PUBLIC-OBJECTION-AND-INVENTORY-DISCOVERY.json',{'scope':'Path/hash discovery in frozen public checkout; file bodies not thereby inspected; not proof that received audit corpus is exhaustive','files':paths})
# Present primary status verbatim, never promote an author preprint to published.
save('PRIMARY-SOURCE-STATUS-RECONCILIATION.json',{'source':bind('research/quartic214/PRIMARY_SOURCES.json'),'role':'verbatim declared publication/access statuses; source statements not all reread','declarations':read('research/quartic214/PRIMARY_SOURCES.json')})
# Exact byte checks only; freshness cannot validate mathematics.
checks=[]
for q in D['coverage_index']:
 loc=q['location'];p=R/loc['pin']['path'];lines=p.read_bytes().splitlines(keepends=True);actual=sha(b''.join(lines[loc['start_line']-1:loc['end_line']]))
 checks.append({'id':q['id'],'pin_matches':sha(p.read_bytes())==loc['pin']['sha256'],'excerpt_matches':actual==loc['excerpt_sha256']})
partitions=[]
for source in [M,T]:
 rr=[q for q in I['records']if q['source']==source];n=len((R/source).read_bytes().splitlines());partitions.append({'source':source,'passages':len(rr),'line_count':n,'contiguous_complete':rr[0]['start']==1 and rr[-1]['end']==n and all(a['end']+1==b['start']for a,b in zip(rr,rr[1:]))})
summary={'initial_passages':len(rows),'inherited_uses':len(U),'connection_records':len(connections),'coverage_records':len(coverage),'passages_with_candidate_inherited_uses':sum(bool(r['candidate_existing_source_use_ids'])for r in rows),'source_use_ids_without_connection':[u for u in uses if u not in connections],'historical_queue_rows':len(H),'public_candidate_files':len(paths),'partition_checks':partitions,'coverage_binding_checks':checks,'author_contracts':contracts,'source_bindings':[bind(p)for p in [M,T,'research/version16/protocol/DOSSIER.json','research/version16/protocol/CONNECTIONS.json','research/quartic214-manuscript/SOURCE_SPANS.json','research/quartic214-manuscript-review/REVIEW_DECISION.json']]}
save('RECONCILIATION-SUMMARY.json',summary)
print(json.dumps({k:v for k,v in summary.items()if k not in ['coverage_binding_checks','author_contracts','source_bindings']},indent=1))
print('binding failures',[q for q in checks if not q['pin_matches']or not q['excerpt_matches']])
