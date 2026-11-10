# redei-plan log

- start: read tyz-5b, cr5b-sec3 report
- TYZ source re-downloaded to a temp dir: line 363 defines g(d) := #(2 Cl(Q(sqrt(-d)))), squares subgroup (line 998 delta_{2Cl}). Confirms target.
- Mathlib inventory so far: QuadraticAlgebra (field instance via Fact, no NumberField instance, no ring of integers), ClassGroup + finiteness, relNorm/absNorm, Galois primes (ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn, exists_smul_eq_of_isGaloisGroup), Dirichlet (Nat.forall_exists_prime_gt_and_eq_mod), Jacobi reciprocity. NO Hilbert symbol, NO Hasse-Minkowski/Legendre ternary, NO binary forms.
- Route idea: (c) genus characters + Dirichlet + ambiguous classes (G1) + counting; avoids Legendre, G2, integral basis, kernel computation.
- 07:55 lake build ZInQKernel.RouteK.Rank5b.Sec3.TYZ
- 07:59 Probe.lean compiles (statements, sorry); instances Field/CharZero/FiniteDimensional/NumberField/IsGalois/Fintype ClassGroup all inferred for QNeg n
- 08:01 probe: proved card_gal, isIntegral_omega, algNorm_eq, norm_nonneg, odd_card_range_sq_iff, fundamental_identity, exists_conj_eq; plumbing T5bCl_eq_T5b, certifiedRankTYZ_iff (modulo gCl_eq_gBit). Next: write docs/research/redei-plan.md and report.
