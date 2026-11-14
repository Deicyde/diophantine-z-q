#!/usr/bin/env python3
"""leaf-fold6: part f10 = leafq-check's Fold.lean (scratch/leafq-check/Fold.lean), ported after leaf-fold5's TailN.

Edits (each asserted):
* the line `import TailK` is dropped (the module TailO imports TailN, which imports TailK);
* leafq-check's intermediate bundles and theorems are renamed, because leaf-fold5 already has
  `HDec.HSyn.OpenAddedLeaves5` and `HDec.HSyn.sixContactMin_of_open5` (leaf-fold5's names are kept):
    OpenAddedLeaves5..10       -> OpenAddedLeavesQ5..Q10
    sixContactMin_of_open5..10 -> sixContactMin_of_openQ5..Q10
    openAddedLeaves4_of_5      -> openAddedLeaves4_of_Q5
    openAddedLeaves5_of_6      -> openAddedLeavesQ5_of_Q6
  Every other line is verbatim (checked at the end: the text with the renames undone equals the source).
Run from scratch/leaf-fold6."""
import re

SRC = '../leafq-check/Fold.lean'
OUT = 'parts/f10_leafq.lean'
src = open(SRC).read()
lines = src.split('\n')
assert lines[0] == 'import TailK', lines[0]
body = '\n'.join(lines[1:])

RENAMES = [
    (r'\bopenAddedLeaves4_of_5\b', 'openAddedLeaves4_of_Q5'),
    (r'\bopenAddedLeaves5_of_6\b', 'openAddedLeavesQ5_of_Q6'),
    (r'\bOpenAddedLeaves(5|6|7|8|9|10)\b', r'OpenAddedLeavesQ\1'),
    (r'\bsixContactMin_of_open(5|6|7|8|9|10)\b', r'sixContactMin_of_openQ\1'),
]
out = body
counts = {}
for pat, rep in RENAMES:
    out, n = re.subn(pat, rep, out)
    counts[pat] = n
    assert n > 0, pat
# no unrenamed leafq-check name remains
assert not re.search(r'\bOpenAddedLeaves(5|6|7|8|9|10)\b', out)
assert not re.search(r'\bsixContactMin_of_open(5|6|7|8|9|10)\b', out)
# undoing the renames gives the source back
back = out
back = re.sub(r'\bopenAddedLeaves4_of_Q5\b', 'openAddedLeaves4_of_5', back)
back = re.sub(r'\bopenAddedLeavesQ5_of_Q6\b', 'openAddedLeaves5_of_6', back)
back = re.sub(r'\bOpenAddedLeavesQ(5|6|7|8|9|10)\b', r'OpenAddedLeaves\1', back)
back = re.sub(r'\bsixContactMin_of_openQ(5|6|7|8|9|10)\b', r'sixContactMin_of_open\1', back)
assert back == body
hdr = ('/-! ## leaf-fold6, part f10: leafq-check\'s `Fold.lean`, ported after leaf-fold5\'s chain (made by `mk_f10.py`:\n'
       '`import TailK` dropped; leafq-check\'s `OpenAddedLeaves5`-`10`, `sixContactMin_of_open5`-`10`,\n'
       '`openAddedLeaves4_of_5`, `openAddedLeaves5_of_6` renamed with a `Q`; nothing else changed). -/\n')
open(OUT, 'w').write(hdr + out)
for k, v in counts.items():
    print(v, k)
print('wrote', OUT, len(out.split('\n')), 'lines')
