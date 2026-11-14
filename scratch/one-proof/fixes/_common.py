"""Generic fixes applied to every regenerated H module (op-dedupe): dot notation on the kernel's `PkgI4.GaloisRep`
for HDec predicates (the field lookup goes to the kernel namespace, where these do not exist)."""
import re, sys
F = sys.argv[1]
s = open(F).read()
n = 0
for pred in ['HasHTWeightsAtSelf', 'DistinctHTWeights']:
    s, k = re.subn(r"(?<![\w.'`])([ρr][\w']*)\." + pred + r"\b", r"PkgI4.GaloisRep." + pred + r" (ρ := \1)", s)
    n += k
open(F, 'w').write(s)
print('common fixes:', n)
# explicit references `_root_.HDec.Y` / `HDec.Y` to a removed copy (or a field/constructor of one) -> kernel `Y`
import pathlib
R = pathlib.Path('scratch/one-proof')
kept = set(l.split()[0] for l in (R / 'kept.txt').read_text().splitlines() if l.strip())
dele = set(r.split('\t')[3] for r in (R / 'dedupe_map.tsv').read_text().splitlines() if r.strip()) - kept
dele |= set(l.split('\t')[1] for l in (R / 'extra_deleted.tsv').read_text().splitlines() if l.strip())
def sub(m):
    y = m.group(2); parts = y.split('.')
    for k in range(len(parts), 0, -1):
        if '.'.join(parts[:k]) in dele: return '_root_.' + y
    return m.group(0)
s = open(F).read()
s2 = re.sub(r"(?<![\w.'])(_root_\.HDec\.|HDec\.)([\w'.]*[\w'])", sub, s)
print('HDec. references redirected:', sum(1 for a, b in zip(s.split('\n'), s2.split('\n')) if a != b), 'lines')
open(F, 'w').write(s2)
