"""Extra check: analytic rank (PARI ellanalyticrank) and root number of C_d for the CR3-hypothesis
curves of cmp40.json with d < 2*10^6 (beyond that the L-series needs too many coefficients)."""
import json
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2 * 10**9)
pari.set_real_precision(19)
out = []
for r in json.load(open('cmp40.json')):
    if r['lean_card'] != 8 or not r['cr3_hyp'] or r['d'] >= 2 * 10 ** 6:
        continue
    d = r['d']
    E = pari.ellinit([-d * d, 0])
    ar = pari.ellanalyticrank(E)
    out.append(dict(d=d, rootno=int(pari.ellrootno(E)), anrank=int(ar[0]), Lderiv=str(ar[1])))
    print(d, 'root number', int(pari.ellrootno(E)), 'analytic rank', int(ar[0]), "L^(r)(1) =", ar[1], flush=True)
json.dump(out, open('anrank.json', 'w'), indent=0)
