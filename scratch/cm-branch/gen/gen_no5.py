"""cm-branch: generate No5 copies (R5ptProps := True) of every declaration upward-affected by the moduli row
in the closure of sixContactMin_of_open67_cm. Skeleton replay of each source module (scope commands kept),
kept declarations copied verbatim with every copied name `c` renamed `c_no5`."""
import re, sys, os
ROOT=os.path.expanduser('~/dzq-wt/cm-branch')
rows=[l.rstrip('\n').split('\t') for l in open(ROOT+'/scratch/cm-branch/affected.tsv') if '\t' in l]
structs={}
decls=[]
for n,k,m,a,b in rows:
    mm=re.match(r'\(some \((\d+), (\S+)\)\)',m)
    idx,mod=int(mm.group(1)),mm.group(2)
    if k=='ind':
        structs[n]=(idx,mod,int(a),int(b))
for n,k,m,a,b in rows:
    if k in ('ctor','ind') or '_proof_' in n: continue
    mm=re.match(r'\(some \((\d+), (\S+)\)\)',m); idx,mod=int(mm.group(1)),mm.group(2)
    pre_=n.rsplit('.',1)[0]
    if pre_ in structs and a!='-' and structs[pre_][1]==mod and structs[pre_][2]<=int(a)<=structs[pre_][3]: continue
    decls.append((n,idx,mod,int(a),int(b)))
def struct_end(mod,a):
    L=open(ROOT+'/'+mod.replace('.','/')+'.lean').read().split('\n')
    i=a  # a is 1-based header line (or docstring start); find 'structure' line
    while not L[i-1].lstrip().startswith(('structure','class')): i+=1
    j=i
    while j<len(L) and (L[j].startswith(' ') or L[j].strip()=='' and j+1<len(L) and L[j+1].startswith(' ')): j+=1
    return j
for s,(idx,mod,a,b) in structs.items(): decls.append((s,idx,mod,a,b))
# exclusions: R5ptProps itself is replaced by a `True` def; my own Top/Open4 files are regenerated separately
EXCL={'LeafQM.AV.R5ptProps','GRDict.GonzalezRotgerThm512X6','GR512Bridge.GonzalezRotgerThm512X6RCF'}
SKIPMOD=set()
keep=[d for d in decls if d[0] not in EXCL and d[2] not in SKIPMOD]
names=set(d[0] for d in decls)  # rename set includes Top/Open4 names and R5ptProps
last={}
for n in names:
    c=n.rsplit('.',1)[-1]
    last.setdefault(c,set()).add(n)
comps=sorted(last, key=len, reverse=True)
IDC=r"A-Za-z0-9_'!?₀-₉ᵢ-ᵪₓ²³′"
pat=re.compile(r"(?<![%s])(%s)(?![%s])"%(IDC,'|'.join(re.escape(c) for c in comps),IDC))
def rename(t):
    return pat.sub(lambda m: m.group(1)+'_no5', t)
SCOPE=re.compile(r'^(namespace|section|end|open|variable|universe|set_option|noncomputable section|attribute \[local|local |scoped |include |omit )')
def skeleton(path, ranges):
    L=open(path).read().split('\n')
    keepset=[]  # (a,b)
    out=[]
    inside=None
    starts={a:b for a,b in ranges}
    i=0; comment=0
    stack=[]
    while i<len(L):
        ln=i+1; l=L[i]
        if ln in starts:
            b=starts[ln]
            # include an immediately preceding `open ... in` / `set_option ... in`
            if out and re.match(r'^(open|set_option) .* in\s*$', out[-1]) is None:
                pass
            if i>0 and re.match(r'^(open|set_option|include|omit|attribute|variable) .* in\s*$', L[i-1]): out.append(L[i-1])
            out.extend(L[i:b]); out.append('')
            i=b; continue
        s=l.strip()
        if comment>0 or s.startswith('/-'):
            # track block comments (nested)
            comment+=l.count('/-')-l.count('-/')
            if comment<0: comment=0
            i+=1; continue
        if SCOPE.match(l) and not re.match(r'^(open|set_option|include|omit|attribute|variable) .* in\s*$', l):
            if l.startswith('namespace') and ' end ' in l:  # one-line export alias block
                i+=1; continue
            w=l.split()
            if w[0]=='namespace': stack.append(('namespace',w[1]))
            elif w[0]=='section': stack.append(('section',w[1] if len(w)>1 else ''))
            elif l.startswith('noncomputable section'): stack.append(('section',w[2] if len(w)>2 else ''))
            elif w[0]=='end':
                if stack: stack.pop()
            l=re.sub(r'^((?:local|scoped) instance )([A-Za-z0-9_]+)', lambda m: m.group(1)+m.group(2)+'_cmb', l)
            out.append(l)
            j=i+1
            while j<len(L) and L[j].startswith('  '):
                out.append(L[j]); j+=1
            i=j; continue
        i+=1
    for kind,nm in reversed(stack):
        out.append('end' + ((' '+nm) if nm else ''))
    return out
mods={}
for d in keep: mods.setdefault((d[1],d[2]),[]).append(d)
order=sorted(mods)
chunks=[]
for idx,mod in order:
    path=ROOT+'/'+mod.replace('.','/')+'.lean'
    rng=sorted(set((d[3],d[4]) for d in mods[(idx,mod)]))
    sk=skeleton(path,rng)
    extra=''
    body=rename('\n'.join(sk))
    if 'SGRDirect' in mod:
        # a root `structure X` (EGAProperLimit/.../CounterexampleCodimension) is in scope here: write Polynomial.X
        body=re.sub(r"(?<![\w.'\[])X(?![\w'\]])(?!\s*:=)", 'Polynomial.X', body)
    if mod=='ZInQKernel.HDecomp.QM.Pin':
        extra='namespace HDec.LeafQM export _root_.LeafQM (AV.R5ptProps_no5 AV.R1R2fp_no5 AV.R1R2fp_Y_no5 AV.exists_fibre_object_no5 AV.residue_unramified_over_branch_no5 AV.Pin.cm_objects_of_R1R2fp_no5) end HDec.LeafQM\n'
    chunks.append((mod,'-- ==== from '+mod+' ====\n'+body+'\n-- ==== end '+mod+' ====\n'+extra))
print('decls kept',len(keep),'modules',len(order), file=sys.stderr)
for mod,c in chunks: print(mod, len(c), file=sys.stderr)
open('/tmp/no5_chunks.txt','w').write('\n'.join(c for m,c in chunks))
import json; json.dump([(m,c) for m,c in chunks], open('/tmp/no5_chunks.json','w'))
json.dump(sorted(names), open('/tmp/no5_names.json','w'))

open('/tmp/no5_all.lean','w').write('\n'.join(c for m,c in chunks))
