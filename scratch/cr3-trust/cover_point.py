"""cr3-trust: find a non-torsion point on C_d via PARI ell2cover + hyperellratpoints
(used for the d where ellrank reports rank 1 without listing a point)."""
import sys, time
import cypari2
pari = cypari2.Pari(); pari.allocatemem(10**9)

def cover_point(d, bounds=(10**3, 10**4, 10**5, 10**6)):
    E = pari.ellinit([0, 0, 0, -d * d, 0])
    for B in bounds:
        for c in pari.ell2cover(E):
            q, m = c[0], c[1]
            for p in pari.hyperellratpoints(q, B):
                Q = pari.subst(pari.subst(m, 'x', p[0]), 'y', p[1])
                if len(Q) == 2 and Q[1] != 0 and pari.ellisoncurve(E, Q):
                    return Q
    return None

if __name__ == "__main__":
    for d in map(int, sys.argv[1:]):
        t = time.time()
        Q = cover_point(d)
        print(d, Q, "%.1fs" % (time.time() - t)); sys.stdout.flush()
