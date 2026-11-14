# import closure of a module within the worktree; usage: closure.py Mod [--has Mod2]
import sys, re, os
def deps(m):
    f = m.replace('.','/')+'.lean'
    if not os.path.exists(f): return []
    return [x for x in re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+(\S+)', open(f).read(), re.M) if x.startswith('ZInQKernel')]
seen=set(); st=[sys.argv[1]]
while st:
    m=st.pop()
    if m in seen: continue
    seen.add(m); st+=deps(m)
if len(sys.argv)>3: print(sys.argv[3] in seen)
else: print('\n'.join(sorted(seen)))
