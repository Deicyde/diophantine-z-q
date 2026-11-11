# Rerun of el-qfree E3 (Hom(Jac Y_theta, C1) = 0 test) on a sample, with positive controls.
import sys, time; sys.path.insert(0, "scratch/el-qfree")
import e3_cmfactor as E
from e3_cmfactor import pari
x = pari('x')
print("control y^2 = x^3 - x, p=19:", E.test(x**3 - x, 19))
print("control y^2 = x^4 - 1, p=23:", E.test(x**4 - 1, 23))
print("control y^2 = x^5 - x, p=19:", E.test(x**5 - x, 19))
print("control y^2 = x^5 + x + 3, p=19 (generic):", E.test(x**5 + x + 3, 19))
for (n, h, s0, eta, m, ps) in [(1, 2, 2, 1, 1, (19, 43)), (1, 2, 2, 1, -1, (19, 47)), (1, 2, 2, -1, 3, (67, 71)),
                                (1, 2, 2, 1, 2, (19, 23, 43, 47))]:
    f = E.curve_poly(n, 1, h, s0, eta, m)
    print((n, h, s0, eta, m), "deg", pari.poldegree(f), flush=True)
    for p in ps:
        if pari.pollead(f) % p == 0: print("   lead divisible", p); continue
        t0 = time.time(); r = E.test(f, p); print("  ", r, f"{time.time()-t0:.0f}s", flush=True)
