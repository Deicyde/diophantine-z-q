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
