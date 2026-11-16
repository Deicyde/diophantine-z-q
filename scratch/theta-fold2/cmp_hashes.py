"""Compare scratch/theta-fold2/hashes_before.txt with hashes_after.txt (name module levels typeHash valueHash).
Writes cmp_hashes_out.txt: removed, new (by module), changed (with whether the type or only the value changed)."""
from collections import Counter
import sys
d = 'scratch/theta-fold2/'
SUF = sys.argv[1] if len(sys.argv) > 1 else ''
def load(f):
    out = {}
    for l in open(d + f):
        if l.strip():
            w = l.split()
            out[w[0]] = w[1:]
    return out
a, b = load(f'hashes_before{SUF}.txt'), load(f'hashes_after{SUF}.txt')
only_a = sorted(set(a) - set(b)); only_b = sorted(set(b) - set(a))
diff = sorted(n for n in set(a) & set(b) if a[n] != b[n])
L = [f'base {len(a)}  after {len(b)}  removed {len(only_a)}  new {len(only_b)}  changed {len(diff)}', '', '## removed']
L += [f'  {n} {a[n][0]}' for n in only_a]
L += ['', '## new, by module'] + [f'  {m}: {c}' for m, c in sorted(Counter(b[n][0] for n in only_b).items())]
L += ['', '## new'] + [f'  {n} {b[n][0]}' for n in only_b]
L += ['', '## changed (T = type hash changed, V = value only)']
L += [f"  {'T' if a[n][2] != b[n][2] else 'V'} {n} {b[n][0]}" for n in diff]
open(d + f'cmp_hashes_out{SUF}.txt', 'w').write('\n'.join(L) + '\n')
print('\n'.join(L))
