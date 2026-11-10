# rv-pd-paper log

## Step 1 (read note, section 1 by hand, Mathlib Dirichlet statement)
- Lean def GoodSlopePrime read (PrimePattern.lean): pointCount = Nat.card{(x,y): y^2=x^3+ax}+1, gcd = 4. Matches note 1.1.
- Lemma 1.1 CORRECT (sum of 1+chi). Lemma 1.2 CORRECT. Lemma 1.3 CORRECT. Lemma 1.4 CORRECT (second moment 2p(p-1), phi(0)=0, square classes).
- Lemma 1.5 CORRECT: g(-D^2/x) = (D^2/x^2)^2 g(x) recomputed; roots +-D swapped by tau, not in X; fixed points +-iD, g(iD) = -2iD^3 != 0, both-or-neither by oddness; m even.
- Prop 1.6 (1)-(4) CORRECT: chi(id)chi(id') = chi(-7) = chi(7) = (p/7) = -1; v2(2(p+1)) = 2 as p = 1 mod 8; odd part argument; n_- = 0 case harmless.
- Lemma 2.1 CORRECT. delta_L = (1/8) prod (l-2)/(l-1) >= 3/(8(L-1)) CORRECT (telescoping over integers 5..floor L).
- Mathlib 56a00585 PrimesInAP.lean:348 LSeries_residueClass_lower_bound: statement exactly as quoted. Lemma 3.1 CORRECT
  (classes disjoint, prime-power contribution <= sum log p/(p(p-1)); Lean needs summability at x>1, dominated by x=1 case).

## Step 2 (computation sec. 1; API statements)
- sec1.py (own implementation, literal Nat.card-style count via square-root table): all 403 class primes p<3e4,
  806 pairs (p,r): c_p odd, p=c^2+e^2, counts {p+1-2c, p+1+2c}, gcd = 4 gcd(c,p+1): NO failure.
  Literal GoodSlopePrime for all odd p<3e4 (347 good) = prediction "class and gcd(c,p+1)=1": no mismatch.
  All odd primes dividing gcd(c_p,p+1) are 1 mod 4.
- Mathlib BoundingSieve fields (SelbergSieve.lean): support, prodPrimes squarefree, weights >= 0, totalMass, nu
  multiplicative with 0<nu p<1 for p|P; SelbergSieve adds level >= 1. The note's data satisfy all. CORRECT.
- PNT at ~/gt-src/PNT is tag v4.35.0 (127b50e3), lake-manifest pins mathlib 56a00585 = ours, toolchain v4.35.0.
  Sieve/{AuxResults,Basic,Selberg,SelbergBounds}.lean: 1536 lines, grep finds no sorry.
  selberg_bound_simple (Selberg.lean:435): siftedSum <= X/S + sum_{d|P} if (d:R) <= y then 3^omega d * |R d| else 0;
  S = sum_{l|P} if l^2 <= y then g l; g = nu.pmul prodPrimeFactors(1/(1-nu p)). Matches note. CORRECT.
  NOTE: note cites tag v4.34.0 and plans a port to 4.35; tag v4.35.0 already on our Mathlib, so no port needed (minor).
- Mathlib names exist: quadraticChar_card_sqrts, quadraticChar_sum_zero, jacobiSum_nontrivial_inv,
  card_fixedPoints_modEq (Function.End, p-power), exists_sq_eq_two_iff, exists_sq_eq_prime_iff_of_mod_four_eq_one,
  exists_sq_eq_neg_one_iff, EM seq bounds (H_n - log(n+1) < gamma < H_n - log n, n>=1), theta_le_log4_mul_x,
  eventually_primeCounting_le (pi floor x <= (log4+eps) x/log x eventually), sum_range_by_parts, totient_mul/prime.

## Step 3 (section 4 and 5 by hand; sec4.py)
- Mathlib BoundingSieve: multSum d = sum_{n in support, d|n} weights n; rem d = multSum d - nu d * totalMass;
  siftedSum = sum_{n in support, Coprime P n} weights n. selbergTerms = nu.pmul prodPrimeFactors (1-nu p)^-1.
  selbergBoundingSum = sum_{l | P, l^2 <= y} g l. PNT v4.35.0 Selberg.lean selberg_bound_simple at line below;
  Sieve files import only Mathlib + Batteries + each other.
- 4.3 set-up CORRECT: F(U,V) >= 1 (b+lV != 0), (4.1) CORRECT (prime p > w coprime to P), M1,M2 <= 2T/l+1.
- Lemma 4.3 CORRECT (also sec4.py: rho(q) = 2q-1 for q<120, l in {5,13,17,29}: 0 failures).
- Lemma 4.4 CORRECT (sec4.py on boxes N up to 1e8: max |R_d|/(2^w(M1+M2+d)) = 0.049).
- 4.4 error term CORRECT: 6^omega <= d^2, #d <= y, M1+M2+y <= 6T/l, 6 N^{-1/10} log N <= 1 at N=1e30.
  Total mass (1+N^{-1/4}/2)^2 <= 5/4 for N >= 324 CORRECT.
- Lemma 4.5 CORRECT: g(q) = (2q-1)/(q-1)^2 >= 2/q; l|P, l^2<=w^2 iff l in D, l<=w, l!=ell-free; ell-terms
  <= (2/ell)S0(w); S >= (3/5)R/V. Claim A CORRECT (|E|<log(1+1/n)<=1/n<=2/t; S1 in [2/3,1]; S2 in [-log3/3,0];
  Mathlib EM lemmas: seq n = H_n - log(n+1) < gamma < seq' n = H_n - log n (n>=1)). Claim B CORRECT
  (prime-power check; V <= 2 zeta(2)^4 = 14.64 via lcm count). sec4.py: r<=h*v n<2e4 ok; min R(w)-bound = 2.77;
  S exact >= bound for w<=1e5, l in {5,13,101,997} (min margin 1.02); R(1e6)=11.50, S0(1e6)=4.74.
- Prop 4.2 constants CORRECT: (logN/60-2)/25 >= logN/1600 iff logN >= 1920; 5*1600+1 = 8001; 2*8001+1.
- Prop 4.1 CORRECT; sum bound 16N^{3/4}+4 sqrt N (1+logN/2) <= 20 N^{3/4} for N>=1e3.
- Lemma 5.1 CORRECT (dyadic + theta <= log4 x). Lemma 5.2 CORRECT. Prop 5.3 CORRECT (Mathlib
  eventually_primeCounting_le is in floor-x form; fine for N nat). Theorem D CORRECT: 0.375/(L) vs 5.545 A1/(L log L)
  gives log L > 14.79 A1; L = e^{240045}.
- sec4.py: Bad_l counts at N=2e6 match 2|C|/(l-1)^2; max bad*l^2 logN/N = 0.42 (l=5); c_17=-1, c_41=-5 as in note.
- Minor Lean-plan issues: sum_quadraticChar_shift_mul as stated is false for p=2 (needs p != 2);
  target now ZInQ.GoodPrimeDensity in GreenTao.lean on main (note still points at scratch gt-search link);
  PNT tag v4.35.0 pins our Mathlib, so file 7 is vendoring not porting.

## Step 4 (PNT sieve compiled against our Mathlib; Mathlib names; sections 1, 6-8 reread)
- Copied PNT v4.35.0 Sieve/{AuxResults,Basic,Selberg}.lean unmodified to scratch/rv-pd-paper/pntsieve/src,
  compiled one at a time with lake env lean -o against Mathlib 56a00585 (load 4, 112 GB free): all compile.
  Check.lean: #check selberg_bound_simple = statement in note; #print axioms -> [propext, Classical.choice,
  Quot.sound]. So Lean-plan file 7 is vendoring, no port; note's open question 1 answered (tag v4.35.0 exists).
- Section 1 reread line by line: Lemmas 1.1-1.5, Prop 1.6 CORRECT (g(tau x) = (D/x)^4 g(x) recomputed).
- Mathlib names: Equiv.Perm.card_fixedPoints_modEq (Function.End, f^(p^n)=1), exists_sq_eq_prime_iff_of_mod_four_eq_one
  (IsSquare (q:ZMod p) <-> IsSquare (p:ZMod q)), quadraticChar_card_sqrts, exists_sq_eq_two_iff, exists_sq_eq_neg_one_iff,
  summable_residueClass_non_primes_div (exponent 1; Lean needs comparison for x>1): all exist as cited.
- Sec 4.6 (not used in the proof): Brun pure sieve reach misstated (z up to exp(c log N/loglog N), saving
  loglog N/log N); conclusion "insufficient" still holds (alpha would grow like loglog N).
- PNT selbergBoundingSum_ge_sum_div indeed assumes CompletelyMultiplicative nu and every prime <= level in P (6.3 CORRECT).
- Verdict forming: proved as written; only minor/editorial findings.
