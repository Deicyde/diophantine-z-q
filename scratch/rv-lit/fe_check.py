"""Conductor and root number of C_d: y^2 = x^3 - d^2 x for squarefree d ≡ 5 (mod 8) (first 30),
and a numeric check of Λ(2-s) = -Λ(s), Λ(s) = N^{s/2}(2π)^{-s}Γ(s)L(s), at a few s in 0<Re s<2 (PARI lfun)."""
import cypari2
pari = cypari2.Pari(); pari.set_real_precision(30)
ds = [d for d in range(5, 2000, 8) if pari.issquarefree(d)][:30]
bad = 0
for d in ds:
    E = pari.ellinit([0, 0, 0, -d*d, 0])
    N = int(pari.ellglobalred(E)[0]); w = int(pari.ellrootno(E))
    ok = (N == 32*d*d and w == -1); bad += not ok
print('d:', ds); print('conductor 32d^2 and root number -1 failures:', bad)
for d in [5, 13, 21]:
    E = pari.ellinit([0, 0, 0, -d*d, 0]); N = 32*d*d
    L = pari.lfuncreate(E)
    for s in [pari('0.3+0.7*I'), pari('1.2-2*I'), pari('0.9')]:
        lam = lambda z: pari(N)**(z/2) * (2*pari.Pi())**(-z) * pari.gamma(z) * pari.lfun(L, z)
        print(d, s, 'Λ(2-s)+Λ(s) =', abs(lam(2-s) + lam(s)))
    print(d, 'L(1) =', pari.lfun(L, 1), " L(2) =", pari.lfun(L, 2), ' ellanalyticrank =', pari.ellanalyticrank(E)[0])
