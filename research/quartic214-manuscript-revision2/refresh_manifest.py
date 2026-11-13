#!/usr/bin/env python3
"""Bind a complete receiving revision without creating independent approval."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def pin(p):
 b=p.read_bytes();return {'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
build=json.loads((HERE/'BUILD.json').read_text())
tex=HERE/'quartic214.tex';pdf=HERE/'quartic214.pdf'
if build['source_files'].get(str(tex.relative_to(ROOT)))!=pin(tex)['sha256']or build['pdf']['sha256']!=pin(pdf)['sha256']:raise ValueError('refuse manifest refresh for stale source/PDF build')
files=[]
for p in sorted(HERE.rglob('*')):
 if p.is_file()and p.name!='MANIFEST.json':
  q=pin(p);q['path']=str(p.relative_to(HERE));files.append(q)
external=[ROOT/p for p in ['research/quartic214-manuscript/quartic214.tex','research/quartic214-manuscript/quartic214.pdf','research/quartic214-manuscript/SOURCE_SPANS.json','research/quartic214-manuscript/assemble.py','research/quartic214-manuscript/build_pdf.py','research/quartic214-manuscript/SOURCE_CORRECTIONS_V1.json','research/quartic214-protocol-d-progress/CURRENT_NATIVE_PRIMITIVE_APPLICATION.json','research/quartic214-protocol-d-progress/PACKET_MANIFEST.json','CURRENT_214_REVIEW.md','.github/workflows/quartic214-manuscript-revision2.yml']]
d={'schema':'q214-complete-receiving-revision2-manifest/v1','role':'author artifact manifest; no independent approval','source_commit':'e3626cac202cdbcdfedc2bff1978dcd3ea3fd3ab','operative_manuscript':'research/quartic214-manuscript-revision2/quartic214.tex','status':'Complete receiving source and matching finalPDF/build; new independent receiving-review binding required','files':files,'external_bindings':[pin(p)for p in external],'self_hash':'Report manifest SHA256 outside this manifest; not embedded','limits':'Original source/artifacts/reports remain frozen historical evidence. This manifest does not renew or manufacture any reviewer acceptance.'}
p=HERE/'MANIFEST.json';p.write_text(json.dumps(d,indent=2)+'\n');print('MANIFEST.json',hashlib.sha256(p.read_bytes()).hexdigest(),'files',len(files))
