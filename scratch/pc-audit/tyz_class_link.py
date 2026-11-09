"""Is the Tian-Yuan-Zhang condition (Smith's bordered determinants) a linear condition on the
non-torsion 2-Selmer class of C_n, when dim Sel_2(C_n) = 3?

For Selmer-minimal squarefree n > 0, n = 5, 6, 7 (mod 8): compute Sel_2(C_n) (sel2cong from
scratch/rv-route-k, cross-checked there against PARI ell2cover), the four non-torsion classes
(a, b) in Kummer coordinates (x, x - n), and 8 basic characters of each class:
  sign(a), v2(a), chi_{-1}(a'), chi_2(a'), and the same for b   (a' = odd part of a)
Search all XOR-combinations (with optional constant) of these 8 bits that are constant on the
coset (torsion-invariant) for every n and agree with the TYZ row determinant.
Usage: tyz_class_link.py NSAMPLES SEED
"""
import sys, random, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'rv-route-k'))
from sel2cong import selmer
import cypari2
from smith22_check import run  # TYZ sums / Smith determinants (agree, see smith22_check)

pari = cypari2.Pari()


def val(mask, gens):
    v = 1
    for i, g in enumerate(gens):
        if mask >> i & 1:
            v *= g
    return v


def feats(a, b):
    out = []
    for x in (a, b):
        s = 1 if x < 0 else 0
        v2 = 1 if x % 2 == 0 else 0
        xo = abs(x) // (2 if v2 else 1)
        cm1 = 1 if xo % 4 == 3 else 0
        c2 = 1 if xo % 8 in (3, 5) else 0
        out += [s, v2, cm1, c2]
    return out


def main():
    N = int(sys.argv[1]); seed = int(sys.argv[2])
    rng = random.Random(seed)
    data = {5: {}, 6: {}, 7: {}}
    cnt = 0
    tried = set()
    while cnt < N:
        if rng.random() < 0.5:
            n = rng.randrange(5, 10 ** 6)
        else:
            ps = rng.sample([int(p) for p in pari.primes(200)][1:], rng.randint(3, 7))
            n = 1
            for p in ps:
                n *= p
            if rng.random() < 0.4:
                n *= 2
        if n in tried or not pari.issquarefree(n) or n % 8 not in (5, 6, 7):
            continue
        tried.add(n)
        odd = [int(p) for p in pari.factor(n)[0] if int(p) != 2]
        basis, gens = selmer(n, odd)
        if len(basis) != 3:
            continue
        cnt += 1
        tors = [(n, 2), (-n, -2 * n), (-1, -n)]
        # find a basis element outside torsion span: compute integer classes
        def sqf(x):
            return int(pari.core(x))
        cls = [(sqf(val(a, gens)), sqf(val(b, gens))) for a, b in basis]
        tset = set()
        for m in range(4):
            A, B = 1, 1
            for j in range(2):
                if m >> j & 1:
                    A *= tors[j][0]; B *= tors[j][1]
            tset.add((sqf(A), sqf(B)))
        # a non-torsion element
        sig = None
        for m in range(1, 8):
            A, B = 1, 1
            for j in range(3):
                if m >> j & 1:
                    A *= cls[j][0]; B *= cls[j][1]
            c = (sqf(A), sqf(B))
            if c not in tset:
                sig = c
                break
        coset = [(sqf(sig[0] * t[0]), sqf(sig[1] * t[1])) for t in tset]
        L, D, _, _, _ = run(n)
        data[n % 8][n] = ([feats(a, b) for a, b in coset], D)
    for t in (5, 6, 7):
        rows = {5: ['5a', '5b'], 6: ['6'], 7: ['7a', '7b']}[t]
        print("class", t, "samples", len(data[t]))
        for row in rows:
            sols = []
            for mask in range(1, 1 << 8):
                for const in (0, 1):
                    ok = True
                    for n, (fs, D) in data[t].items():
                        vals = {(sum(f[i] for i in range(8) if mask >> i & 1) + const) % 2 for f in fs}
                        if len(vals) != 1 or vals.pop() != D[row]:
                            ok = False
                            break
                    if ok:
                        sols.append((mask, const))
            names = ['sgn a', 'v2 a', 'chi-1 a', 'chi2 a', 'sgn b', 'v2 b', 'chi-1 b', 'chi2 b']
            print(" row", row, "nonzero fraction",
                  sum(D[row] for _, D in data[t].values()), "/", len(data[t]),
                  "linear rules:", [(' + '.join(names[i] for i in range(8) if m >> i & 1), c) for m, c in sols])


main()
