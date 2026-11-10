# pd-paper log

## Step 0 (start)
- Fresh run (no earlier log). Branch wip/pd-paper at c399a64.
- Sources read: PrimePattern.lean (GoodSlopePrime, pointCount), PrimeAP.lean (GoodPrimeAP),
  nt-22p.md §2 (CM description, Prop D sketch), rv-nt22p-ap F5 (sieve range needs uniform
  N/(l^2 log N) bound; tail term sqrt(N) log N), aud-ap §1.3–1.4 (finding F1: Prop D unwritten),
  manuscript lines 1554–1642 (conjugate orders, bad prime values).
- Mathlib: worktree manifest mathlib rev 56a005855e = ~/dzq/.lake/packages/mathlib rev; grep there.

## Step 1 (library survey)
- Mathlib 56a00585: `NumberField.dedekindZeta`, `dedekindZeta_residue`, `tendsto_sub_one_mul_dedekindZeta_nhdsGT`
  (class number formula, residue at 1); `NumberField.Set.primeIdealZetaSum`, `HasDirichletDensity`,
  `dirichletDensity` (NumberField/DirichletDensity.lean; basic API only, no Chebotarev);
  `ArithmeticFunction.vonMangoldt.residueClass`, `LSeries_residueClass_lower_bound`,
  `summable_residueClass_non_primes_div`, `Nat.forall_exists_prime_gt_and_modEq` (PrimesInAP.lean);
  Chebyshev: `Chebyshev.theta_le_log4_mul_x`, `eventually_primeCounting_le`, `theta_le_pi_mul_log`, `pi_ge`;
  Selberg skeleton only: `BoundingSieve`, `SelbergSieve`, `siftedSum_le_mainSum_errSum_of_upperMoebius`,
  `upperMoebius_lambdaSquared`, `mainSum_lambdaSquared_eq_sum_mul_sum_sq` (SelbergSieve.lean);
  characters: `quadraticChar_card_sqrts`, `quadraticChar_sum_zero`, `jacobiSum_nontrivial_inv`,
  `ZMod.exists_sq_eq_two_iff`, `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`, `Nat.Prime.sq_add_sq`.
- PrimeNumberTheoremAnd tag v4.34.0 (c39a7511), read via module-proxy zip: Sieve/{Basic,AuxResults,
  Selberg,SelbergBounds}.lean (~1536 lines, 0 sorry): `SelbergSieve.selberg_bound_simple`
  (siftedSum ≤ X/S + Σ_{d|P, d≤y} 3^ω(d)|R_d|), `selberg_bound_weights` (|γ d| ≤ 1),
  `selbergBoundingSum_ge_sum_div` (needs ν completely multiplicative and all primes ≤ y in P: NOT our case);
  BrunTitchmarsh.lean `primesBetween_le` (1-dim example, 0 sorry).
- KEY MATH FINDINGS (to verify numerically):
  (a) "Frobenius" conditions reduce to congruences mod 56: p≡1 (8) and (p/7)=-1; Q(√2,√7,i) abelian.
  (b) CM facts needed have elementary proofs: φ(a)=Σχ(x³+ax); pointCount = p+1+φ(a);
      φ(ak²)=χ(k)φ(a); φ(1)≡2 (mod 4) for p≡1 (4) (orbits x,-x,1/x,-1/x); Jacobsthal
      φ(1)²+φ(r)²=4p (r non-square). Hence t=∓φ(1), p=(t/2)²+(φ(r)/2)², 4|d_i, v2(gcd)=2.
  (c) bad ℓ ⇒ ℓ≡1 (4) (e²≡-1), so ℓ=3,7 and all ℓ≡3 (4) need no condition.
