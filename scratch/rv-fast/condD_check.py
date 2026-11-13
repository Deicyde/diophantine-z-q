# Differential check of ring-class's condD/sqfPart formula (RingClassGalois.lean l.914-956)
# against PARI: for D < 0, D = 0,1 mod 4, the order of discriminant D in K = Q(sqrt D) is Z + f O_K
# with d_K = quaddisc(D), f = sqrtint(D/d_K).  Lean: m = sqfPart|D| (core), and
# condD D = sqrt(|D|/m) if m % 4 == 3 else sqrt(|D|/(4m)); K = Q(sqrt(-m)).
import cypari2
pari = cypari2.Pari()
sample = [-3,-4,-7,-8,-11,-12,-15,-16,-19,-20,-23,-24,-27,-28,-32,-36,-48,-60,-63,-64,
          -75,-99,-108,-128,-192,-320,-448,-832,-1344,-64*13]
bad = 0
for D in sample:
    assert D % 4 in (0, 1)
    dK = int(pari.quaddisc(D)); f = int(pari.sqrtint(D // dK)); assert f*f*dK == D
    m = int(pari.core(-D))
    fl = int(pari.sqrtint((-D)//m)) if m % 4 == 3 else int(pari.sqrtint((-D)//(4*m)))
    dKl = -m if m % 4 == 3 else -4*m
    ok = (fl == f and dKl == dK)
    bad += (not ok)
    print(D, "pari:", dK, f, " lean-formula:", dKl, fl, "OK" if ok else "MISMATCH")
print("mismatches:", bad, "of", len(sample))
