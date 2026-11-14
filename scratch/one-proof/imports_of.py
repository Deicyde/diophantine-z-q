"""imports_of.py MODULE...: print the modules among stdin lines (import X) that transitively import any MODULE."""
import sys, re, pathlib, functools
@functools.lru_cache(None)
def deps(m):
    p = pathlib.Path(m.replace('.', '/') + '.lean')
    if not p.exists(): return frozenset()
    out = set()
    for l in p.read_text(errors='ignore').splitlines():
        mm = re.match(r'^import\s+(ZInQKernel\S*)', l)
        if mm: out.add(mm.group(1)); out |= deps(mm.group(1))
    return frozenset(out)
bad = set(sys.argv[1:])
for l in sys.stdin:
    m = l.split()[1] if l.startswith('import') else None
    if m and (m in bad or deps(m) & bad): print(m)
