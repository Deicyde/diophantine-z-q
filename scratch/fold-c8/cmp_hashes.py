"""Compare two hash dumps (name module levels typeHash valueHash per constant).
Usage: python3 scratch/fold-c8/cmp_hashes.py BEFORE AFTER  (files in scratch/fold-c8/)."""
import sys, collections
d = 'scratch/fold-c8/'
def load(f):
    return {l.split()[0]: l.split(None, 1)[1] for l in open(d + f) if l.strip()}
a, b = load(sys.argv[1]), load(sys.argv[2])
only_a = sorted(set(a) - set(b)); only_b = sorted(set(b) - set(a))
diff = sorted(n for n in set(a) & set(b) if a[n] != b[n])
print(f'before {len(a)}  after {len(b)}  only before {len(only_a)}  only after {len(only_b)}  changed {len(diff)}')
print('changed:', diff)
print('only before:', only_a[:20])
print('modules of new constants:', dict(collections.Counter(b[n].split()[0] for n in only_b)))
