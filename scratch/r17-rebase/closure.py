# usage: closure.py TOPS_FILE MODULE  -> prints the tops whose import closure contains MODULE
import os, re, sys, functools
def path(m): return m.replace('.', '/') + '.lean'
@functools.lru_cache(None)
def imports(m):
    p = path(m)
    if not os.path.exists(p): return ()
    return tuple(mm.group(1) for line in open(p, encoding='utf-8')
                 for mm in [re.match(r'\s*(?:public\s+)?import\s+(ZInQKernel\S*)', line)] if mm)
@functools.lru_cache(None)
def clo(m):
    s = {m}
    for i in imports(m): s |= clo(i)
    return frozenset(s)
sys.setrecursionlimit(100000)
tops = [l.strip() for l in open(sys.argv[1]) if l.strip()]
for t in tops:
    if sys.argv[2] in clo(t): print(t)
