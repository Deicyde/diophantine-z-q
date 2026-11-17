# top-level Contrib modules: under ZInQKernel/Contrib, not imported by another Contrib module
import os, re, sys
root = 'ZInQKernel/Contrib'
mods = {}
for d, _, fs in os.walk(root):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(d, f)
            mods[p[:-5].replace('/', '.')] = p
imported = set()
for m, p in mods.items():
    for line in open(p, encoding='utf-8'):
        mm = re.match(r'\s*import\s+(\S+)', line)
        if mm: imported.add(mm.group(1))
tops = sorted(m for m in mods if m not in imported)
print(len(mods), len(tops), file=sys.stderr)
for t in tops: print(t)
