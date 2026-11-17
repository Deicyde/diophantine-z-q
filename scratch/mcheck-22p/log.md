# mcheck-22p results log

- Statement.lean: Mathlib-only Prop `MCheck22P.FixedPrimePattern` (tex L1267-1289). COMPILED (lake env lean, 2026-11-17).
- orders_small.py/.out: 30 primes p>324, p=1 mod 8, p=3 mod 7, direct point counts. VERIFIED: both reductions good, d1+d2=2(p+1),
  gcd(d1,d2)=4*oddpart(gcd(a,p+1)) with d1=p+1-2a, 2-part of gcd exactly 4, p∤d1d2. gcd≠4 occurs (p=1249: 20; p=3769: 52) —
  excluded in the proof by c_q=1 mod q (q<=324). Contrast sample (7/p)=+1: d1=d2 (gcd=d1), so p=3 mod 7 is needed.
- orders_large.py/.out: 30 random primes (~450 bits) in the full residue pattern of tex L1329-1332; orders via Cornacchia
  candidates + [N]P=O on 4 random points (unique candidate each time). VERIFIED all structural checks; gcd=4 in all 30.
  Part B: 3 pattern primes with 337 | gcd(a,p+1): gcd = 1348 = 4*337. VERIFIED: congruences alone do not give gcd=4;
  the sieve step (tex L1584-1642) is genuinely needed.
