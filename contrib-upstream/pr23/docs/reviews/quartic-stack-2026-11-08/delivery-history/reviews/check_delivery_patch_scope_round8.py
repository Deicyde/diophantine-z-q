"""Independent path and exact-tree review of the two final delivery patches.

Uses a private shared bare clone and its own index/object writes. The supplied
repository, overlays and patches are read only. Both routes are applied to an
index, compared to the complete delivered payload, and compared outside the
proposal prefix to the pinned upstream tree.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import re
import shlex
import subprocess
import tempfile

PIN='036cebe4f1a4aa7ca89820a9b48f3629b4c364d6'
PREFIX='research/conditional-quartic-reduction/'
OLD_MANIFEST='f2d74ebd40b61a48b1b3d1ecdb55d2fda53f372a090fce8ec1fcd347e333bbd5'


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob(value):
    return hashlib.sha1(b'blob '+str(len(value)).encode()+b'\0'+value).hexdigest()


def payload(overlay):
    assert overlay.is_dir() and not overlay.is_symlink()
    entries={}
    for path in sorted(overlay.rglob('*')):
        assert not path.is_symlink(),str(path)
        if path.is_file():
            rel=path.relative_to(overlay).as_posix()
            value=path.read_bytes()
            entries[PREFIX+rel]={'mode':'100755' if path.stat().st_mode&0o111 else '100644','oid':git_blob(value),'sha256':hashlib.sha256(value).hexdigest(),'bytes':len(value)}
    return entries


def verify_manifest(overlay,entries,expected_count):
    doc=json.loads((overlay/'SOURCE_MANIFEST.json').read_text())
    expected={PREFIX+'SOURCE_MANIFEST.json'}
    for item in doc['files']:
        rel=PurePosixPath(item['path'])
        assert not rel.is_absolute() and '..' not in rel.parts and str(rel)==item['path']
        path=PREFIX+str(rel)
        assert path not in expected
        expected.add(path)
        assert entries[path]['sha256']==item['sha256'] and entries[path]['bytes']==item['bytes']
    assert expected==set(entries) and len(entries)==expected_count
    return len(doc['files'])


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--repository',type=Path,required=True)
    parser.add_argument('--bundle',type=Path,required=True)
    parser.add_argument('--baseline',type=Path,required=True)
    parser.add_argument('--work-root',type=Path,required=True)
    parser.add_argument('--report',type=Path,required=True)
    args=parser.parse_args()
    repository=args.repository.resolve();bundle=args.bundle.resolve();baseline=args.baseline.resolve()
    overlay=bundle/'payload'/PREFIX
    delivered=payload(overlay);prior=payload(baseline)
    new_entries=verify_manifest(overlay,delivered,156)
    old_entries=verify_manifest(baseline,prior,112)
    assert sha256(baseline/'SOURCE_MANIFEST.json')==OLD_MANIFEST
    nested=overlay/'lineage/round7_delivery/SOURCE_MANIFEST.json'
    assert sha256(nested)==OLD_MANIFEST,'Frozen nested historical manifest is absent or changed'
    helper=bundle/'verify_update_base.py';helper_before=sha256(helper)
    patches={'full':bundle/'proposed-change.patch','update':bundle/'update-from-392.patch'}
    patch_hashes={k:sha256(p) for k,p in patches.items()}
    header_summary={}
    for route,path in patches.items():
        files=[];header=False;new_count=0;deleted_count=0;renamed_count=0
        for line in path.read_text().splitlines():
            if line.startswith('diff --git '):
                parts=shlex.split(line)
                assert len(parts)==4 and parts[:2]==['diff','--git']
                pair=[]
                for prefix,value in zip(['a/','b/'],parts[2:]):
                    assert value.startswith(prefix)
                    rel=value[len(prefix):];pure=PurePosixPath(rel)
                    assert rel.startswith(PREFIX) and not pure.is_absolute() and '..' not in pure.parts and str(pure)==rel
                    pair.append(rel)
                renamed_count+=pair[0]!=pair[1]
                files.append(pair[1]);header=True
            elif header and (line.startswith('@@') or line=='GIT binary patch'):
                header=False
            elif header:
                if line.startswith(('--- ','+++ ')):
                    value=line[4:].split('\t',1)[0]
                    if value!='/dev/null':
                        assert value.startswith(('a/'+PREFIX,'b/'+PREFIX)),value
                if line.startswith(('new file mode ','deleted file mode ','old mode ','new mode ')):
                    assert line.split()[-1] in ['100644','100755'],line
                    new_count+=line.startswith('new file mode ')
                    deleted_count+=line.startswith('deleted file mode ')
                if line.startswith(('rename from ','rename to ','copy from ','copy to ')):
                    value=line.split(' ',2)[2]
                    pure=PurePosixPath(value)
                    assert value.startswith(PREFIX) and not pure.is_absolute() and '..' not in pure.parts and str(pure)==value
        assert files and len(set(files))==len(files)
        if route=='full':assert len(files)==156 and new_count==156 and deleted_count==0
        header_summary[route]={'fileSections':len(files),'newFiles':new_count,'deletedFiles':deleted_count,'renamedFilesWithinProposal':renamed_count,'allPathsWithinProposal':True,'allModesRegularFiles':True}
    args.work_root.mkdir(parents=True,exist_ok=True)
    work=Path(tempfile.mkdtemp(prefix='patch-scope-',dir=args.work_root.resolve()))
    bare=work/'review.git'
    subprocess.run(['git','clone','--bare','--shared',str(repository),str(bare)],check=True,capture_output=True)
    def git(*arguments,input=None):
        cp=subprocess.run(['git','--git-dir='+str(bare),*arguments],input=input,capture_output=True,check=True)
        return cp.stdout
    assert git('rev-parse','--show-object-format').strip()==b'sha1'
    def tree_entries(tree):
        result={}
        for record in git('ls-tree','-r','-z','--full-tree',tree).split(b'\0'):
            if not record:continue
            info,name=record.split(b'\t',1);mode,kind,oid=info.decode().split()
            assert kind=='blob'
            result[name.decode()]={'mode':mode,'oid':oid}
        return result
    upstream=tree_entries(PIN)
    assert not any(p.startswith(PREFIX) for p in upstream),'Pinned upstream already contains an overlay'
    def index_entries():
        result={}
        for record in git('ls-files','--stage','-z').split(b'\0'):
            if not record:continue
            info,name=record.split(b'\t',1);mode,oid,stage=info.decode().split()
            assert stage=='0'
            result[name.decode()]={'mode':mode,'oid':oid}
        return result
    wanted={name:{'mode':v['mode'],'oid':v['oid']} for name,v in delivered.items()}
    routes=[]
    for route,patch in patches.items():
        git('read-tree','--reset','-i',PIN)
        if route=='update':
            relative=sorted(prior)
            filepaths=[str(baseline/name[len(PREFIX):]) for name in relative]
            objects=git('hash-object','-w','--stdin-paths',input=('\n'.join(filepaths)+'\n').encode()).decode().splitlines()
            assert len(objects)==112
            instructions=[]
            for name,oid in zip(relative,objects):
                assert oid==prior[name]['oid']
                instructions.append(prior[name]['mode']+' '+oid+'\t'+name+'\n')
            git('update-index','--add','--index-info',input=''.join(instructions).encode())
            old_index=index_entries()
            assert {k:v for k,v in old_index.items() if not k.startswith(PREFIX)}==upstream
            assert {k:v for k,v in old_index.items() if k.startswith(PREFIX)}=={k:{'mode':v['mode'],'oid':v['oid']} for k,v in prior.items()}
        git('apply','--cached','--check','--whitespace=nowarn',str(patch))
        git('apply','--cached','--whitespace=nowarn',str(patch))
        result=index_entries()
        actual={k:v for k,v in result.items() if k.startswith(PREFIX)}
        outside={k:v for k,v in result.items() if not k.startswith(PREFIX)}
        assert actual==wanted,'Patch result does not equal delivered payload including modes'
        assert outside==upstream,'Patch changed pinned upstream outside proposal prefix'
        tree=git('write-tree').decode().strip()
        routes.append({'route':route,'gitApplyCheck':True,'gitApply':True,'payloadFilesCompared':len(actual),'identicalContentAndModesToPayload':True,'upstreamFilesOutsideProposalUnchanged':len(outside),'resultTree':tree,'indexOnly':True})
    assert routes[0]['resultTree']==routes[1]['resultTree']
    assert payload(overlay)==delivered and payload(baseline)==prior
    assert {k:sha256(p) for k,p in patches.items()}==patch_hashes
    assert sha256(helper)==helper_before
    report={'status':'PASS','upstreamCommit':PIN,'allowedPrefix':PREFIX,'patches':{k:{'path':str(p),'sha256':patch_hashes[k],**header_summary[k]} for k,p in patches.items()},'routes':routes,'identicalResultTree':routes[0]['resultTree'],'currentSourceManifestSha256':sha256(overlay/'SOURCE_MANIFEST.json'),'currentManifestEntries':new_entries,'currentPayloadFiles':len(delivered),'oldSourceManifestSha256':OLD_MANIFEST,'oldManifestEntries':old_entries,'oldPayloadFiles':len(prior),'nestedHistoricalManifestPreserved':True,'helperSha256':helper_before,'allSuppliedInputsUnchanged':True,'privateReviewRepository':str(bare),'checkerSha256':sha256(Path(__file__)),'scope':'Exact Git index application, regular-file modes, full156-file payload equality and preservation of every pinned upstream file outside the proposal. Mathematical reproduction and inherited global inputs are separate.'}
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
