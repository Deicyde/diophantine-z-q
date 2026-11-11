#!/usr/bin/env python3
"""Check exact public port bindings and table equality, not mathematical acceptance."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    m=json.loads((HERE/'SOURCE_PATH_MAP.json').read_text())
    checked=0
    for e in m['reused_public_sources']:
        assert sha(ROOT/e['public_path'])==e['sha256'],e['public_path'];checked+=1
    for e in m['selected_private_sources']:
        assert sha(ROOT/e['public_path'])==e['public_sha256'],e['public_path'];checked+=1
    for alias,path in m['reading_aliases'].items():assert (ROOT/path).is_file(),(alias,path)
    def verify_binding(e):
        p=ROOT/e['path'];assert p.is_file(),e['path']
        raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==e['sha256'],e['path']
        if 'bytes' in e:assert len(raw)==e['bytes'],e['path']
        if 'lines' in e:
            a,b=e['lines'];assert 1<=a<=b<=len(raw.splitlines()),e['path']
            assert hashlib.sha256(b''.join(raw.splitlines(keepends=True)[a-1:b])).hexdigest()==e['passage_sha256'],(e['path'],e['lines'])
    index=json.loads((HERE/'contracts/INDEX.json').read_text())
    for row in index['contracts']:
        verify_binding(row)
        contract=json.loads((ROOT/row['path']).read_text())
        assert len(contract['obligations'])==row['obligations']==9,row['path']
        assert contract['independent_acceptance'] is None,row['path']
        for key in ('manuscript','proof'):verify_binding(contract[key])
        for key in ('construction_passages','application_passages','consumer_passages','required_sources'):
            assert contract[key],(row['path'],key)
            for evidence in contract[key]:verify_binding(evidence)
        for obligation in contract['obligations'].values():
            for key in ('required_input','constructed_input','justification'):assert obligation[key],(row['path'],key)
            for key in ('source_references','evidence'):
                assert obligation[key],(row['path'],key)
                for evidence in obligation[key]:verify_binding(evidence)
    carry=json.loads((HERE/'contracts/source-carry-sources.json').read_text())
    for item in carry['matches']:
        verify_binding(item['new_consumer'])
        for key in ('actual_proof_sources','source_receipts'):
            for evidence in item[key]:verify_binding(evidence)
    scopes=json.loads((HERE/'sources/public-provider-scopes.json').read_text())
    for scope in scopes['sources']:verify_binding(scope['public_source'])
    manifest=json.loads((HERE/'AUTHOR_MANIFEST.json').read_text())
    current={str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p.name not in ('AUTHOR_MANIFEST.json',) and '__pycache__' not in p.parts}
    assert current==set(manifest['files']),current.symmetric_difference(manifest['files'])
    for path,digest in manifest['files'].items():assert sha(HERE/path)==digest,path
    for p in HERE.rglob('*'):
        if p.is_file() and p.suffix in ('.py','.json','.md','.tex'):
            text=p.read_text()
            assert not re.search(r'/' + r'(?:tmp|home)/',text),str(p.relative_to(HERE))
    ir=json.loads((HERE/'construction/artifacts/candidate214-brox/candidate214-ir.json').read_text())
    poly=json.loads((HERE/'construction/artifacts/candidate214-brox/candidate214-polynomial.json').read_text())
    assert ir['variables']==poly['variables']==214 and len(ir['residuals'])==188
    assert poly['degree']==4 and poly['inputCoordinate']==1
    print(json.dumps({'status':'PASS','sourceBindings':checked,'manifestFiles':len(current),'authorContracts':len(index['contracts']),'variables':214,'rows':188,'scope':'Portable paths, exact source and author-file bindings, table metadata only; no mathematical or independent acceptance.'},indent=2))
if __name__=='__main__':main()
