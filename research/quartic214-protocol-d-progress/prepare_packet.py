#!/usr/bin/env python3
"""Prepare additive evidence copies from the explicitly authorized scratch packet."""
from pathlib import Path
import gzip,hashlib,json,shutil,resource
ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
SCRATCH=Path('/tmp/q214-d-next-20261112')
def digest(data):return hashlib.sha256(data).hexdigest()
def install(src,dst):
 data=src.read_bytes();target=OUT/dst;target.parent.mkdir(parents=True,exist_ok=True)
 if len(data)>=100000:
  target=target.with_name(target.name+'.gz')
  with target.open('wb')as f:
   with gzip.GzipFile(filename='',mode='wb',compresslevel=9,mtime=0,fileobj=f)as z:z.write(data)
 else:target.write_bytes(data)
 return {'path':str(target.relative_to(OUT)),'logical_path':dst,'sha256':digest(target.read_bytes()),'bytes':target.stat().st_size,'uncompressed_sha256':digest(data),'uncompressed_bytes':len(data),'compression':'gzip-mtime0-no-name'if target.suffix=='.gz'else'none','source_provenance':str(src),'copy_scope':'original bytes unchanged after decompression'}
def main():
 resource.setrlimit(resource.RLIMIT_AS,(512*1024*1024,512*1024*1024))
 entries=[]
 for p in sorted((SCRATCH/'inventory').iterdir()):
  if p.is_file()and p.name not in ['FABLE-AUDIT-TEXT.txt','make_direct_contract.py']:entries.append(install(p,'inventory/'+p.name))
 for name in ['V16-PROTECTED-CHECK.json','V16-NATIVE-IDENTITY.json','V16-NATIVE-REUSE-NOTE.json']:
  entries.append(install(SCRATCH/'root'/name,'provenance/'+name))
 for lane in ['rc','analytic','geometry','history-review']:
  base=SCRATCH/lane
  # Reviewer-authored evidence only. No PDF, image or extracted third-party text.
  if not((base/'REVIEW.md').exists()or(base/'REPORT.md').exists()):continue
  if lane=='rc':
   allowed=[q['path']for q in json.loads((base/'MANIFEST.json').read_text())['files']]+['MANIFEST.json']
  elif lane=='analytic':
   allowed=list(json.loads((base/'REPORT_MANIFEST.json').read_text()))+['REPORT_MANIFEST.json']
  else:
   allowed=[q['path']for q in json.loads((base/'MANIFEST.json').read_text())['files']]+['MANIFEST.json']
  for name in sorted(set(allowed)):
   p=base/name
   if p.suffix.lower()not in ['.json','.md','.py','.sha256']:raise ValueError('excluded source format '+name)
   entries.append(install(p,'reviews/'+lane+'/'+name))
 # The reviewer request precedes the final geometry report and is itself needed now.
 p=SCRATCH/'geometry'/'DIRECT_EDGE_REQUEST.json'
 if p.exists()and not any(e['logical_path']=='reviews/geometry/'+p.name for e in entries):entries.append(install(p,'reviews/geometry/'+p.name))
 mathematical=json.loads((SCRATCH/'closure-review/MATHEMATICAL_MANIFEST.json').read_text())
 for name in [q['path']for q in mathematical['files']]+['MATHEMATICAL_MANIFEST.json']:
  p=SCRATCH/'closure-review'/name
  if p.exists():entries.append(install(p,'reviews/closure-review/'+name))
 continuation=json.loads((SCRATCH/'closure-review/COVERAGE_LINK_MANIFEST.json').read_text())
 for name in [q['path']for q in continuation['files']]+['COVERAGE_LINK_MANIFEST.json']:
  entries.append(install(SCRATCH/'closure-review'/name,'reviews/closure-review/'+name))
 external=[]
 native=['.github/workflows/quartic214-protocol-d-progress.yml','manuscripts/quartic_v16.tex','research/version16/protocol/DOSSIER.json','research/version16/protocol/CONNECTIONS.json','research/version16/review/coverage/record-repair-001/REVIEW.md','research/version16/review/coverage/record-repair-001/REVIEW.json','research/version16/review/coverage/record-repair-001/PROTOCOL14-COVERAGE-REVIEW.json','research/version16/review/coverage/record-repair-001/ASSEMBLY-REVIEW.json','research/version16/protocol/record-repair-001/REPAIR.json','research/quartic214-manuscript/quartic214.tex','research/quartic214-manuscript/quartic214.pdf','research/quartic214/contracts/modularity-6.json']
 native+=['research/quartic214/contracts/INDEX.json']+[q['path']for q in json.loads((ROOT/'research/quartic214/contracts/INDEX.json').read_text())['contracts']]
 for lane,name,key in [('rc','source-bindings.json','whole_files'),('analytic','BINDINGS.json','files')]:
  for q in json.loads((SCRATCH/lane/name).read_text())[key]:
   p=ROOT/q['path']
   if digest(p.read_bytes())!=q['sha256']:raise ValueError('Reviewer source differs: '+q['path'])
   native.append(q['path'])
 for q in json.loads((SCRATCH/'geometry/REVIEWED_FILE_PINS.json').read_text()):
  if digest((ROOT/q['path']).read_bytes())!=q['sha256']:raise ValueError('Geometry source differs: '+q['path'])
  native.append(q['path'])
 for name in ['M1_BINDINGS.json','M3_M6_BINDINGS.json']:
  binding=SCRATCH/'closure-review'/name
  if binding.exists():
   for q in json.loads(binding.read_text())['pins']:
    if digest((ROOT/q['path']).read_bytes())!=q['sha256']:raise ValueError('Modularity source differs: '+q['path'])
    native.append(q['path'])
 for name in ['SOURCE_PINS.json','READ_PASSAGES.json']:
  for q in json.loads((SCRATCH/'history-review'/name).read_text()):
   if digest((ROOT/q['path']).read_bytes())!=q['sha256']:raise ValueError('History source differs: '+q['path'])
   native.append(q['path'])
 for q in json.loads((SCRATCH/'closure-review/CURRENT_SECTION_COVERAGE.json').read_text())['sections']+json.loads((SCRATCH/'closure-review/FROZEN_ARTIFACT_IDENTITY.json').read_text()):
  if digest((ROOT/q['path']).read_bytes())!=q['sha256']:raise ValueError('Assembly source differs: '+q['path'])
  native.append(q['path'])
 contract=json.loads((OUT/'CURRENT_NATIVE_PRIMITIVE_APPLICATION.json').read_text())
 for q in contract['passages']+[contract['manuscript'],contract['pdf'],contract['existing_contract'],contract['source_metadata']]:
  if digest((ROOT/q['path']).read_bytes())!=q['sha256']:raise ValueError('Primitive application source differs: '+q['path'])
  native.append(q['path'])
 for name in sorted(set(native)):
  p=ROOT/name;external.append({'path':name,'sha256':digest(p.read_bytes()),'bytes':p.stat().st_size,'bundled':False,'role':'existing frozen repository evidence; preserved in place'})
 pdf_paths={ROOT/'research/version16/audits/fable-5-2-audit-4.pdf'}
 for lane in ['primary','rc','analytic','geometry']:pdf_paths.update((SCRATCH/lane).rglob('*.pdf'))
 for p in sorted(pdf_paths):
  if p.exists():external.append({'path':str(p),'sha256':digest(p.read_bytes()),'bytes':p.stat().st_size,'bundled':False,'role':'external third-party primary source; not distributed in this additive packet'})
 (OUT/'EVIDENCE_MANIFEST.json').write_text(json.dumps({'schema':'q214-progress-evidence/v1','role':'author packaging record; no approval','source_commit':'e3626cac202cdbcdfedc2bff1978dcd3ea3fd3ab','entries':entries,'external_bindings':external,'exclusions':['FABLE-AUDIT-TEXT.txt and all other extracted third-party source text','third-party PDFs and images','private repositories and controller-private evidence'],'limits':'Original reviewer manifests retain their original paths and source-access limitations. Compressed copies preserve exact original uncompressed bytes. Manifest itself is externally hashed by PACKET_MANIFEST.json.'},indent=2)+'\n')
 print('Evidence copied',len(entries),'stored bytes',sum(e['bytes']for e in entries),'logical bytes',sum(e['uncompressed_bytes']for e in entries))
if __name__=='__main__':main()
