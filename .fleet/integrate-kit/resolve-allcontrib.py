#!/usr/bin/env python3
"""Resolve a merge conflict in AllContrib.lean made only of import lines: keep main's (theirs) lines, then ours.
Exits 2 (file untouched) if any conflict hunk holds a non-import line, or if the result has duplicate lines."""
import sys
p = sys.argv[1] if len(sys.argv) > 1 else 'ZInQKernel/Contrib/AllContrib.lean'
L = open(p).read().split('\n')
out, i = [], 0
while i < len(L):
    if L[i].startswith('<<<<<<< '):
        m = next(j for j in range(i, len(L)) if L[j] == '=======')
        b = next(j for j in range(m, len(L)) if L[j].startswith('>>>>>>> '))
        ours, theirs = L[i + 1:m], L[m + 1:b]
        if any(x.strip() and not x.startswith('import ') for x in ours + theirs):
            print('non-import line in a conflict hunk'); sys.exit(2)
        out += theirs + ours; i = b + 1
    else:
        out.append(L[i]); i += 1
imports = [x for x in out if x.startswith('import ')]
if len(imports) != len(set(imports)):
    print('duplicate imports after resolution'); sys.exit(2)
open(p, 'w').write('\n'.join(out))
print(f'resolved: {len(imports)} imports')
