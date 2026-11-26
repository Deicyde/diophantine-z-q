import sys
std = {'propext', 'Classical.choice', 'Quot.sound'}
for f in sys.argv[1:]:
    t = ' '.join(open(f).read().split())
    segs = t.split('depends on axioms:')[1:]
    bad = []
    for seg in segs:
        ax = {a.strip() for a in seg.split(']')[0].strip().lstrip('[').split(',')}
        if not ax <= std:
            bad.append(sorted(ax - std))
    none = t.count('does not depend on any axioms')
    print(f.split('/')[-1], 'head', t.split()[0][:8], 'decls', len(segs) + none, 'nonstandard', len(bad), bad[:3], 'sorry' if 'sorry' in t else 'no-sorry', 'target-ok' if 'FrozenTarget matches' in t else 'TARGET?')
