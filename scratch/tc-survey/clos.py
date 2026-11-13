# usage: clos.py ROOT MODULE...  -> closure size, lines, and count NOT in vendored-kwnew.txt
import os,re,sys
root=sys.argv[1]; mods=sys.argv[2:]
V=set(l.strip() for l in open(os.path.join(os.path.dirname(__file__),'vendored-kwnew.txt')))
def p(m): return os.path.join(root,*m.split('.'))+'.lean'
def deps(m):
    f=p(m)
    if not os.path.exists(f): return []
    out=[]
    for line in open(f,encoding='utf-8',errors='replace'):
        mm=re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)',line)
        if mm and mm.group(1).startswith('TauCeti'): out.append(mm.group(1))
    return out
S=set(); st=list(mods)
while st:
    x=st.pop()
    if x in S: continue
    S.add(x); st.extend(deps(x))
miss=[x for x in S if not os.path.exists(p(x))]
lines=sum(sum(1 for _ in open(p(x),encoding='utf-8',errors='replace')) for x in S if os.path.exists(p(x)))
new=[x for x in S if x not in V]
nl=sum(sum(1 for _ in open(p(x),encoding='utf-8',errors='replace')) for x in new if os.path.exists(p(x)))
print(f'{len(S)} modules, {lines} lines, {len(miss)} missing; not yet vendored: {len(new)} modules, {nl} lines')
if os.environ.get('OUT'): open(os.environ['OUT'],'w').write('\n'.join(sorted(new))+'\n')
