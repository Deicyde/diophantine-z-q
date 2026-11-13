"""Freeze and package the complete current public research state over published V16."""
import argparse, hashlib, io, json, re, shutil, subprocess, zipfile
from contextlib import ExitStack
from pathlib import Path, PurePosixPath

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
MANIFEST=HERE/'MANIFEST.json'
SELF='research/version17/MANIFEST.json'
STAMP=(2026,11,13,0,0,0)
DENIED={'.git','.aws','.codex','.ssh','.venv','node_modules','__pycache__','conversations','sessions'}

def digest_stream(stream):
    h=hashlib.sha256()
    for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
def digest(path):
    with path.open('rb') as f:return digest_stream(f)
def safe_name(name):
    p=PurePosixPath(name)
    if p.is_absolute() or not p.parts or any(x in ('','..') for x in p.parts) or '\\' in name or ':' in name:
        raise ValueError('Unsafe path: '+name)
    if any(x.lower() in DENIED for x in p.parts) or p.name.lower() in {'credentials.json','tokens.json','id_rsa','id_ed25519','conversation.json','transcript.jsonl'} or p.name.startswith('.env') or p.suffix.lower() in {'.pem','.key','.pyc'}:
        raise ValueError('Disallowed private/runtime path: '+name)
    return p.as_posix()
class GitTree:
    """Immutable raw Git blobs. No checkout conversion or archive export filters."""
    def __init__(self,root,object_id):
        self.root=Path(root).resolve()
        if not re.fullmatch(r'(?:[0-9a-fA-F]{40}|[0-9a-fA-F]{64})',object_id):
            raise ValueError('--tree must be an immutable full Git object ID')
        self.command=['git','--no-replace-objects','-c','safe.directory='+str(self.root)]
        self.oid=subprocess.check_output(self.command+['rev-parse','--verify',object_id+'^{tree}'],cwd=self.root,text=True).strip()
        raw=subprocess.check_output(self.command+['ls-tree','--full-tree','-r','-l','-z',self.oid],cwd=self.root)
        self.files={};self.hashes={}
        for item in raw.split(b'\0'):
            if not item:continue
            metadata,name=item.split(b'\t',1);mode,kind,oid,size=metadata.split()
            name=safe_name(name.decode('utf-8'))
            if kind!=b'blob' or mode not in (b'100644',b'100755'):
                raise ValueError('Only regular Git files may be packaged: '+name)
            self.files[name]={'git_blob':oid.decode(),'git_mode':mode.decode(),'bytes':int(size)}
        self.process=subprocess.Popen(self.command+['cat-file','--batch'],cwd=self.root,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    def __enter__(self):return self
    def __exit__(self,*exc):
        self.process.stdin.close();self.process.stdout.close()
        self.process.wait(timeout=10)
    def copy(self,name,sink=None):
        record=self.files[name];oid=record['git_blob']
        self.process.stdin.write((oid+'\n').encode());self.process.stdin.flush()
        header=self.process.stdout.readline().split()
        if header!=[oid.encode(),b'blob',str(record['bytes']).encode()]:
            raise ValueError('Unexpected raw Git object header: '+repr(header))
        left=record['bytes'];h=hashlib.sha256()
        while left:
            block=self.process.stdout.read(min(left,1024*1024))
            if not block:raise ValueError('Truncated Git blob: '+name)
            h.update(block);left-=len(block)
            if sink is not None:sink.write(block)
        if self.process.stdout.read(1)!=b'\n':raise ValueError('Missing Git object terminator')
        value=h.hexdigest();self.hashes[oid]=value;return value
    def read(self,name):
        sink=io.BytesIO();self.copy(name,sink);return sink.getvalue()
    def record(self,name):
        item=dict(self.files[name]);oid=item['git_blob']
        value=self.hashes.get(oid)
        if value is None:value=self.copy(name)
        return dict(path=name,sha256=value,**item)
def config(tree):
    cfg=json.loads(tree.read('research/version17/HANDOFF-BASE.json'))
    if cfg['manifest_excludes']!=[SELF,'SHA256SUMS']:
        raise ValueError('Only the manifest and SHA256SUMS may be cycle exclusions')
    return cfg
def check_base(previous,cfg):
    if previous.stat().st_size!=cfg['previous_archive_bytes'] or digest(previous)!=cfg['previous_archive_sha256']:
        raise ValueError('Not the exact published Version 16 archive')
def base_inventory(previous,cfg):
    """Hash actual effective known-layer bytes; unknown older paths are not omitted."""
    found={}
    with ExitStack() as stack:
        outer=stack.enter_context(zipfile.ZipFile(previous))
        opened={():outer}
        for layer in cfg['verified_base_layers_in_order']:
            chain=tuple(layer[:-1]);prefix=layer[-1]
            if chain not in opened:
                z=outer;partial=[]
                for member in chain:
                    partial.append(member);key=tuple(partial)
                    if key not in opened:
                        stream=stack.enter_context(z.open(member));opened[key]=stack.enter_context(zipfile.ZipFile(stream))
                    z=opened[key]
            z=opened[chain]
            for info in z.infolist():
                if info.is_dir() or not info.filename.startswith(prefix):continue
                name=safe_name(info.filename[len(prefix):])
                with z.open(info) as stream:sha=digest_stream(stream)
                found[name]={'sha256':sha,'bytes':info.file_size,'executable':bool((info.external_attr>>16)&0o111),'base_member_chain':list(chain)+[info.filename]}
    return found
def select(tree,cfg,allow_missing=False):
    names=set(tree.files);missing=[]
    for addition in cfg['additional_paths']:
        safe_name(addition)
        if addition not in names and not any(n.startswith(addition.rstrip('/')+'/') for n in names):missing.append(addition)
    if missing and not allow_missing:raise ValueError('Required public additions not frozen: '+', '.join(missing))
    names.difference_update(cfg['manifest_excludes'])
    return sorted(names),missing
def snapshot(tree,previous,cfg,allow_missing=False):
    check_base(previous,cfg);base=base_inventory(previous,cfg);names,missing=select(tree,cfg,allow_missing)
    records=[]
    for name in names:
        row=tree.record(name)
        old=base.get(name)
        if old and all(old[k]==row[k] for k in ('sha256','bytes')) and old['executable']==(row['git_mode']=='100755'):
            row.update(delivery='verified_base',base_member_chain=old['base_member_chain'])
        else:row['delivery']='overlay'
        records.append(row)
    return records,missing
def summary(rows,missing):
    overlay=[r for r in rows if r['delivery']=='overlay']
    return {'current_files':len(rows),'current_uncompressed_bytes':sum(r['bytes'] for r in rows),
            'overlay_files':len(overlay),'overlay_uncompressed_bytes':sum(r['bytes'] for r in overlay),
            'verified_base_files':len(rows)-len(overlay),'missing_required_additions':missing}
def put(z,path,name,stored=False):
    info=zipfile.ZipInfo(name,STAMP);info.compress_type=zipfile.ZIP_STORED if stored else zipfile.ZIP_DEFLATED
    info.external_attr=0o100644<<16
    with path.open('rb') as src,z.open(info,'w',force_zip64=True) as dst:shutil.copyfileobj(src,dst,1024*1024)
def put_text(z,name,text):
    info=zipfile.ZipInfo(name,STAMP);info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
    z.writestr(info,text.encode('utf-8'))
def put_git(z,tree,row):
    info=zipfile.ZipInfo('overlay/'+row['path'],STAMP);info.compress_type=zipfile.ZIP_DEFLATED
    info.create_system=3;info.external_attr=int(row['git_mode'],8)<<16
    with z.open(info,'w',force_zip64=True) as dst:actual=tree.copy(row['path'],dst)
    if actual!=row['sha256']:raise ValueError('Git blob differs from frozen row: '+row['path'])
def execute(args,tree):
    cfg=config(tree);rows,missing=snapshot(tree,args.previous,cfg,args.plan)
    if args.plan:print(json.dumps(dict(summary(rows,missing),source_git_tree=tree.oid,source_bytes='raw-git-blobs'),indent=2));return
    if args.freeze_manifest:
        obj={'schema':'version17-current-research-handoff/v2','version':17,
             'previous_archive_sha256':cfg['previous_archive_sha256'],'previous_archive_bytes':cfg['previous_archive_bytes'],
             'inventory_source_git_tree':tree.oid,'source_bytes':'raw-git-blobs',
             'scope':'Every regular file in the explicitly selected Git tree, except the two cycle exclusions. Git blobs and executable bits are preserved without checkout normalization or archive export filters. Historical byte/mode matches are individually verified.',
             'cycle_exclusions':cfg['manifest_excludes'],'files':rows}
        MANIFEST.write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8',newline='\n');print(json.dumps(dict(summary(rows,missing),inventory_source_git_tree=tree.oid),indent=2));return
    manifest=json.loads(tree.read(SELF))
    if manifest.get('source_bytes')!='raw-git-blobs' or manifest['previous_archive_sha256']!=cfg['previous_archive_sha256'] or manifest['files']!=rows:
        raise ValueError('Selected Git tree differs from frozen manifest; review and re-freeze before packaging')
    output=args.output.resolve()
    if output.is_relative_to(ROOT):raise ValueError('Archive output must be outside the checkout')
    temporary=output.with_name(output.name+'.partial')
    if output.exists() or temporary.exists() or output.with_name(output.name+'.sha256').exists():raise ValueError('Refusing to overwrite archive, partial archive or checksum')
    extra=[dict(tree.record(name),delivery='overlay') for name in cfg['manifest_excludes']]
    overlay=[r for r in rows if r['delivery']=='overlay']+extra
    output.parent.mkdir(parents=True,exist_ok=True)
    historical='historical/'+cfg['previous_archive_name']
    with zipfile.ZipFile(temporary,'w',allowZip64=True,compresslevel=6) as z:
        put(z,args.previous,historical,True)
        for row in sorted(overlay,key=lambda r:r['path']):put_git(z,tree,row)
        put_text(z,'OVERLAY-MANIFEST.json',json.dumps(overlay,indent=2)+'\n')
        put_text(z,'CURRENT-TREE.json',json.dumps({'git_tree':tree.oid,'source_bytes':'raw-git-blobs','files':sorted(rows+extra,key=lambda r:r['path'])},indent=2)+'\n')
        put_text(z,'README.txt','Version 17 cumulative research handoff\n\nPreserve the historical Version 16 ZIP unchanged and reconstruct it separately using its own instructions. For the exact current Git publication, populate a fresh directory with only the paths in CURRENT-TREE.json: take overlay entries here and verified-base entries from their recorded historical member chains. Preserve the listed Git executable bits. This leaves all historical archives unchanged. A cumulative research workspace may retain additional historical files, but those are not part of the exact current Git tree. No checkout newline conversion or git-archive export filter was applied. Read research/version17/CUMULATIVE-HANDOFF.md.\n')
    with zipfile.ZipFile(temporary) as z:
        with z.open(historical) as stream:
            if digest_stream(stream)!=cfg['previous_archive_sha256']:raise ValueError('Historical archive readback failed')
        for row in overlay:
            info=z.getinfo('overlay/'+row['path'])
            if (info.external_attr>>16)!=int(row['git_mode'],8):raise ValueError('Git mode readback failed: '+row['path'])
            with z.open(info) as stream:
                if digest_stream(stream)!=row['sha256']:raise ValueError('Overlay readback failed: '+row['path'])
    temporary.rename(output)
    result=dict(summary(rows,missing),source_git_tree=tree.oid,source_bytes='raw-git-blobs',archive=output.name,archive_bytes=output.stat().st_size,archive_sha256=digest(output),previous_archive_sha256=cfg['previous_archive_sha256'])
    output.with_name(output.name+'.sha256').write_text(result['archive_sha256']+'  '+output.name+'\n',encoding='ascii')
    print(json.dumps(result,indent=2))
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--previous',type=Path,required=True);p.add_argument('--tree',required=True,help='Full immutable Git tree or commit object ID; use git write-tree after staging')
    mode=p.add_mutually_exclusive_group(required=True);mode.add_argument('--plan',action='store_true');mode.add_argument('--freeze-manifest',action='store_true');mode.add_argument('--output',type=Path)
    args=p.parse_args()
    with GitTree(ROOT,args.tree) as tree:execute(args,tree)
if __name__=='__main__':main()
