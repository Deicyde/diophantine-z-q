import re, sys, os
roots = sys.argv[1:]
seen = set(); stack = list(roots)
while stack:
    m = stack.pop()
    if m in seen or not m.startswith('ZInQKernel'): continue
    seen.add(m)
    p = m.replace('.', '/') + '.lean'
    for l in open(p):
        mm = re.match(r'import (\S+)', l)
        if mm: stack.append(mm.group(1))
for m in sorted(seen):
    if 'TauCeti' not in m: print(m)
