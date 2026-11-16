import re,sys,os
def imports(mod):
    p=mod.replace('.','/')+'.lean'
    if not os.path.exists(p): return []
    return [l.split()[1] for l in open(p) if l.startswith('import ')]
def closure(m):
    seen=set();st=[m]
    while st:
        x=st.pop()
        if x in seen: continue
        seen.add(x); st+=imports(x)
    return seen
c=closure(sys.argv[1])
for x in sorted(c):
    if x.startswith('ZInQKernel.OneProof') or x.startswith('ZInQKernel.Contrib.OneProof'): print(x)
