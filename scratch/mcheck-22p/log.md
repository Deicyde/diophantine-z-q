# mcheck-22p results log

- Statement.lean: Mathlib-only Prop `MCheck22P.FixedPrimePattern` (tex L1267-1289). COMPILED (lake env lean, 2026-11-17).
- orders_small.py/.out: 30 primes p>324, p=1 mod 8, p=3 mod 7, direct point counts. VERIFIED: both reductions good, d1+d2=2(p+1),
  gcd(d1,d2)=4*oddpart(gcd(a,p+1)) with d1=p+1-2a, 2-part of gcd exactly 4, p∤d1d2. gcd≠4 occurs (p=1249: 20; p=3769: 52) —
  excluded in the proof by c_q=1 mod q (q<=324). Contrast sample (7/p)=+1: d1=d2 (gcd=d1), so p=3 mod 7 is needed.
- orders_large.py/.out: 30 random primes (~450 bits) in the full residue pattern of tex L1330-1333; orders via Cornacchia
  candidates + [N]P=O on 4 random points (unique candidate each time). VERIFIED all structural checks; gcd=4 in all 30.
  Part B: 3 pattern primes with 337 | gcd(a,p+1): gcd = 1348 = 4*337. VERIFIED: congruences alone do not give gcd=4;
  the sieve step (tex L1600-1643) is genuinely needed.
- local_densities.py/.out: VERIFIED for q in {331,337}, 6 values of A each: 1-22/q <= P(all F≠0) <= 1-22/q+231/q^2 and
  log beta_q >= -484/q^2; fibre union of 21 distinct lines, size in [21q-210, 21q] (q=331, 4 cases); 22/q^5<1 for all q<=324;
  rational majorant q^2(log(1-22/q)-22log(1-1/q)) >= -242.72 >= -484 for q>=325.
- Finite.lean: COMPILED. forms_length, unit_coeff, pairwise_minor (every pair of the 22 forms has an A-free nonzero minor
  of size <=61, all A), contact_diffs, norm_d (=7), seven_nonsq_of_three_mod7, two_sq_of_one_mod8, ineqs, class_infinite
  (Dirichlet), prime_coprime_W.
- l954_polys.py/.out: l1(57600F^2)+l1(G^6) = 3.571e21 <= 2*4000^6 = 8.192e21; log(2*4000^6) = 50.46 < 74. VERIFIED.
- L954.lean: COMPILED, axioms propext/Classical.choice/Quot.sound. height_bound: max(|p|,q) <= 2*4000^6*max(|a|,b)
  (|p| <= 3600^6|a|, q <= 57600 b + 117649|a|, degenerate case j=-57600/117649 gives q | 686 or q | 7007);
  log_height_bound; log_const_lt.
- No error found. No .fleet verdict file written.
