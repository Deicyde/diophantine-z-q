"""Markdown tables for .fleet/cr3-check.md from cmp40.json, points40.json and slot5.json."""
import json, os
rows = json.load(open('cmp40.json'))
import glob
pts = [p for f in sorted(glob.glob('points40_*.json')) for p in json.load(open(f))]
P = {(p['d'], p['a']): p for p in pts}
for f in sorted(glob.glob('points2_*.json')):
    for p in json.load(open(f)):
        if p['found'] or (p['d'], p['a']) not in P or not P[(p['d'], p['a'])]['found']:
            P[(p['d'], p['a'])] = p
if os.path.exists('quartic_found.txt'):
    for line in open('quartic_found.txt'):
        w = line.split()
        if 'FOUND' in w and 'NOT' not in w:
            k = (int(w[0]), int(w[1]))
            if k not in P or not P[k]['found']:
                P[k] = dict(d=k[0], a=k[1], found=True, how='quartic search ' + w[2])
print('| d | primes (class mod 8) | Lean #sols | dim Sel₂: Lean / indep / rv sel2.py / PARI | Sel₂ sets equal | a with \\|a\\| ≡ 7 and Lean σ.first = natClass d a | CR₃ hyp. | point with x ∈ aℚ*² (a > 0 / a < 0) |')
print('|---|---|---|---|---|---|---|---|')
for r in rows:
    hyp = r['lean_card'] == 8 and r['a7_lean']
    a7 = ', '.join(str(a) for a in r['a7_lean'] if a > 0)
    a7 = ('±' + a7.replace(', ', ', ±')) if a7 else '—'
    if hyp:
        res = []
        for a in r['cr3_hyp']:
            p = P.get((r['d'], a))
            res.append('?' if p is None else ('found (%s)' % p['how'] if p['found'] else 'not found'))
        pt = ' / '.join(res)
    else:
        pt = '—'
    print('| %d | %s | %d | %d / %d / %d / %d | %s | %s | %s | %s |' % (
        r['d'], ' '.join('%d (%d)' % (p, p % 8) for p in r['primes']), r['lean_card'], r['lean_dim'],
        r['indep_dim'], r['rv_dim'], r['pari_dim'], 'yes' if r['same_group'] and r['firsts_ok'] else 'NO',
        a7, 'yes' if hyp else 'no', pt))
