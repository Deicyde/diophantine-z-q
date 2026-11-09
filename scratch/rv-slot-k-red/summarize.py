"""Table of the adversarial batches: runs, certified, ranges of omega(beta), omega(theta), slots."""
import re, glob, sys
fams = ['theta1', 'omega1', 'all3mod4', 'mostly1mod4', 'thetacls', 's0beta', 'allm', 'p0var', 'cores',
        'cores_extra', 'slope_site', 'test_site', 'test_site_b', 'small_slots', 'large', 'random30']
tot = [0, 0]
for f in fams:
    try:
        L = open('out_%s.txt' % f).read().splitlines()
    except FileNotFoundError:
        continue
    runs = [l for l in L if l.startswith('#')]
    ok = [l for l in runs if l.rstrip().endswith('OK') or ' OK q0=' in l]
    bad = [l for l in runs if 'FAIL' in l]
    wb = [int(x) for x in re.findall(r'w\(b\)=(\d+)', '\n'.join(runs))]
    wt = [int(x) for x in re.findall(r'w\(t\)=(\d+)', '\n'.join(runs))]
    sl = [int(x) for x in re.findall(r'slots=(\d+)', '\n'.join(runs))]
    sg = set(re.findall(r'beta=([+-])', '\n'.join(runs)))
    tot[0] += len(runs); tot[1] += len(ok)
    print("| `%s` | %d | %d | %d | %d-%d | %d-%d | %d-%d | %s |" % (f, len(runs), len(ok), len(bad), min(wb), max(wb),
          min(wt), max(wt), min(sl), max(sl), ''.join(sorted(sg))))
print("total runs %d certified %d" % tuple(tot))
