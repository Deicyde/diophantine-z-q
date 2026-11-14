"""Compare hashes_before.txt with hashes_after.txt (name module levels typeHash valueHash per constant)."""
import sys
d = 'scratch/one-proof/'
def load(f):
    return {l.split()[0]: l.split(None, 1)[1] for l in open(d + f) if l.strip()}
a, b = load('hashes_before.txt'), load('hashes_after.txt')
only_a = sorted(set(a) - set(b)); only_b = sorted(set(b) - set(a))
diff = sorted(n for n in set(a) & set(b) if a[n] != b[n])
print(f'before {len(a)}  after {len(b)}  only before {len(only_a)}  only after {len(only_b)}  changed {len(diff)}')
for n in (only_a + only_b + diff)[:40]: print(' ', n, a.get(n), '|', b.get(n))
