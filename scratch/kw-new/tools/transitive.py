"""transitive.py MODULE... : for the given nov01 modules (new), find decls added after oct16 to shared
modules that they use, transitively through the bodies of those added decls."""
import sys,os,re
sys.path.insert(0,os.path.dirname(__file__))
from decls import decls,p
H=os.path.expanduser('~'); O=H+'/tc-oct16'; N=H+'/tc-nov01'
allm=[l.strip() for l in open(H+'/dzq-runs/tc/kw-all.txt') if l.strip()]
new=set(l.strip() for l in open(H+'/dzq-runs/tc/kw-new-nov01.txt') if l.strip())
shared=[m for m in allm if m not in new]
added={}
for m in shared:
    o=set(decls(p(O,m))); n=set(decls(p(N,m)))
    for x in n-o: added[x]=m
KW=r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)'
def blocks(m):
    L=open(p(N,m),encoding='utf-8').read().split('\n'); res={}
    stack=[]
    for i,line in enumerate(L):
        mm=re.match(r'^namespace\s+(\S+)',line)
        if mm: stack.append(mm.group(1))
        mm=re.match(r'^end\s+(\S+)',line)
        if mm and stack and stack[-1]==mm.group(1): stack.pop()
        mm=re.match(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*'+KW+r'\s+([^\s:({\[]+)',line)
        if mm:
            e=i+1
            while e<len(L) and not (L[e].strip()=='' and (e+1>=len(L) or L[e+1][:1] not in (' ',''))): e+=1
            n=mm.group(1); full=n[7:] if n.startswith('_root_.') else ('.'.join(stack+[n]) if stack else n)
            res[full]='\n'.join(L[i:e])
    return res
BL={}
def body(x):
    m=added[x]
    if m not in BL: BL[m]=blocks(m)
    return BL[m].get(x,'')
idx={}
for x in added:
    parts=x.split('.')
    for c in {parts[-1],'.'.join(parts[-2:])}:
        if len(c)>=5: idx.setdefault(c,set()).add(x)
def uses(txt):
    toks=set(re.findall(r"[A-Za-z_][\w.'₀-₉]*",txt))
    out=set()
    for t in toks:
        parts=t.split('.')
        for k in range(len(parts)):
            s='.'.join(parts[k:])
            if s in idx: out|=idx[s]
    return out
seeds=set()
for m in sys.argv[1:]:
    seeds|=uses(open(p(N,m),encoding='utf-8').read())
need=set(); st=list(seeds)
while st:
    x=st.pop()
    if x in need: continue
    need.add(x); st.extend(uses(body(x))-need)
bym={}
for x in need: bym.setdefault(added[x],[]).append(x)
tot=0
for m in sorted(bym):
    ln=sum(body(x).count('\n')+1 for x in bym[m]); tot+=ln
    print(f'{m}  ({len(bym[m])} decls, ~{ln} lines)')
    for x in sorted(bym[m]): print('   ',x)
print('total lines',tot)
