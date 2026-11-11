# Check the conventions of the Lean Props in Literature.lean against PARI, on 20 curves C_d.
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2*10**9)
ds = [d for d in range(5, 4000, 8) if pari.issquarefree(d)][::9][:20]
bad = 0
for d in ds:
    E = pari.ellinit([0, 0, 0, -d*d, 0])
    gr = pari.ellglobalred(E)
    N = int(gr[0]); w = int(pari.ellrootno(E))
    minimal = (list(gr[1]) == [1, 0, 0, 0])          # change of variables to minimal model is trivial
    badp = [int(p) for p in pari.factor(2*d)[0]]
    loc_ok = all(int(pari.ellap(E, p)) == 0 and int(pari.elllocalred(E, p)[1]) not in (1,) for p in badp)
    kod = [int(pari.elllocalred(E, p)[1]) for p in badp]   # Kodaira code; >4 or <-4... additive iff code not In (I_n, n>=1 coded as 4+n) nor 0
    additive = all(not (k > 4) and k != 0 for k in kod)
    good_ok = True
    for p in pari.primes(40):
        p = int(p)
        if p in badp: continue
        cnt = 1 + sum(1 for x in range(p) for y in range(p) if (y*y - x**3 + d*d*x) % p == 0)
        if int(pari.ellap(E, p)) != p + 1 - cnt: good_ok = False
    ok = (N == 32*d*d) and (w == -1) and minimal and loc_ok and additive and good_ok
    bad += not ok
    print(d, N == 32*d*d, w, minimal, kod, loc_ok, good_ok, "OK" if ok else "FAIL")
print("failures:", bad, "of", len(ds))
