"""fold-b100: compare scratch/fold-b100/hashes_base.txt (base Main's imports; base frozenTarget is in the scratch file,
so it is not listed) with hashes_after.txt. Usage: python3 scratch/fold-b100/cmp_hashes.py [base] [after]"""
import sys
d = 'scratch/fold-b100/'
fa = sys.argv[1] if len(sys.argv) > 1 else 'hashes_base.txt'
fb = sys.argv[2] if len(sys.argv) > 2 else 'hashes_after.txt'
def load(f):
    return {l.split()[0]: l.split(None, 1)[1] for l in open(d + f) if l.strip()}
a, b = load(fa), load(fb)
only_a = sorted(set(a) - set(b)); only_b = sorted(set(b) - set(a))
diff = sorted(n for n in set(a) & set(b) if a[n] != b[n])
print(f'base {len(a)}  after {len(b)}  removed {len(only_a)}  added {len(only_b)}  changed {len(diff)}')
for n in only_a[:20]: print('  removed', n)
for n in diff[:20]: print('  changed', n, a[n], '|', b[n])
mods = sorted({b[n].split()[0] for n in only_b})
print('  added constants in modules:', ', '.join(mods))
