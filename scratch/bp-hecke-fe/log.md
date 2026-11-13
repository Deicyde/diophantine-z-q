# bp-hecke-fe results log

## Theta.lean (VERIFIED: compiles, no sorry, `lake env lean`, 2026-11-12 ~17:40)
- `gaussTheta a b x = oddKernel a x · evenKernel b x + i · evenKernel a x · oddKernel b x`
  (= Σ_{(m,n)∈ℤ²} ((m+a)+i(n+b)) e^{−π((m+a)²+(n+b)²)x}), dual with sinKernel/cosKernel.
- `gaussTheta_one_div`: gaussTheta a b (1/x) = x² · gaussThetaDual a b x (x > 0).
- `gaussFEPair`, `isStrong_gaussFEPair`: strong FE-pair, k = 2, ε = 1.
- `differentiable_gaussLambda` (Mellin transform entire), `gaussLambda_two_sub`
  (Λ(2 − s) = Λ^dual(s)), `mellinConvergent_gaussTheta` (all s).
- (VERIFIED, compiled ~18:05) `hasSum_gaussTheta`: gaussTheta a b t = Σ_{p∈ℤ²} gz·exp(−π gq t)
  (product of Mathlib's 1-D kernel sums, absolutely summable).
- `gaussPeriodPair` (ℤ + ℤi as Mathlib `PeriodPair`), `summable_norm_gz_rpow` (r < −2, via
  `ZLattice.summable_norm_sub_rpow`).
- `hasSum_gaussLambda`: for Re s > 3/2, Σ_p π^{−s}Γ(s) gz/gq^s = gaussLambda a b s.
- `gaussL_continuation`: the shifted lattice series Σ_p ((m+a)+i(n+b))/((m+a)²+(n+b)²)^s has an
  entire continuation F(s) = π^s Γ(s)⁻¹ Λ(s) from Re s > 3/2.
- (VERIFIED, compiled ~17:45) `twistedL M c s = Σ'_{p∈ℤ²} c(p mod M)·(p₁+ip₂)/(p₁²+p₂²)^s`;
  `summable_twisted` (Re s > 3/2), `twistedL_eq` (block decomposition into M² shifted series,
  via `blockEquiv : (Fin M)² × ℤ² ≃ ℤ²`), `twistedL_continuation`: entire continuation for
  every c : (ZMod M)² → ℂ.
- Built `ZInQKernel.RouteK.Rank.LFunctionCd` (43 s) and `ZInQKernel.Hypotheses.CR3Literature`
  (lake build, needed for the scratch import). File renamed Theta.lean → HeckeFE.lean.
- (VERIFIED, compiled ~17:52; `#print axioms` = propext, Classical.choice, Quot.sound)
  `normFiber`, `mem_normFiber`, `LSeries_eq_twistedL` (grouping the lattice sum by the norm),
  `unitOf` (primary-unit normalisation mod 4), `cdChar d` on (ZMod 4d)², `cdChar_intCast`,
  `heckeCoeff d n = ¼ Σ_{N α = n} (Nα/d)·unitOf(α)·α`, `DeuringCd d : Prop`
  (cdCoeff d n = heckeCoeff d n for n ≠ 0), `isLContinuation_of_deuring`
  (odd squarefree d: DeuringCd d → ∃ F, IsLContinuation (C_d) F),
  `heckeContinuation5_of_deuring`.

## Numerical checks (VERIFIED, PARI via cypari2)
- `deuring_check.py` → `out_deuring_check.txt`: a_n(C_d) = heckeCoeff d n for n ≤ 400,
  d ∈ {1,5,13,21,29,37,53,85}: 0 mismatches. Conductor 32d², root number −1 (d ≡ 5 mod 8), +1 (d=1).
- `fourier_check.py` → `out_fourier_check.txt`: finite Fourier transform of the character data:
  2-part g₂(ν) = Σ_{j mod 4} unitOf(j) e(j·ν/4) = 4(1+i)·unitOf(ν/(1+i)) (support ν ≡ (1+i)·odd);
  odd part Σ_{j mod d} (Nj/d) e(j·ν/d) = d·(Nν/d) for d ∈ {5,13,21,3,7} (all ν mod d).
- (VERIFIED, compiled ~17:55) `ech a b p = e(a p₁ + b p₂)`, `hasSum_gaussThetaDual`
  (dual kernel = Σ_p −i·gz₀₀(p)·e(a p₁ + b p₂)·exp(−π gq₀₀(p) t)), `hasSum_gaussLambdaDual`
  (its Mellin transform as a lattice Dirichlet series, Re s > 3/2).
- (VERIFIED, compiled ~18:00) `fourierHat M c ν = Σ_j c(j) e(j·ν/M)`, `lambdaC M c = Σ_j c(j) Λ_{j/M}`
  (entire), `lambdaC_eq` (π^{−s}Γ(s)T_c(s) = M (M²)^{−s} Λ_c(s), Re s > 3/2), `dual_eq`,
  `FourierRel M c κ : Prop` (ĉ((1+i)μ) = κ c(μ), ĉ = 0 off (1+i)ℤ[i]), `fourierRel_const_mul`,
  `mulOneAddI_injective`, `fourier_tsum_eq`, `lambdaC_two_sub`:
  FourierRel M c κ → ∀ s, Λ_c(2−s) = −iκ(1+i)·2^{−s}·M·(M²)^{−s}·Λ_c(s) (identity theorem).
- (VERIFIED, compiled ~18:05; axioms propext, Classical.choice, Quot.sound)
  `CdFourier d := FourierRel (4d) (cdChar d) (4d(1+i)(2/d))`, `jacobiSym_two_of_mod_eight`,
  `cpow_of_pos`, `const_identity` (conductor bookkeeping N = 32d² = 2M²),
  `functionalEquation5_of_deuring_fourier` (one d) and
  `functionalEquation5_of_deuring_fourier' : (∀ d ≡ 5 (8) sqfree, DeuringCd d) →
   (∀ such d, CdFourier d) → ZInQ.Literature.FunctionalEquation5`  (the Literature Prop itself).
- (VERIFIED numerically) full `CdFourier d` as defined, all ν mod 4d, d ∈ {5, 13, 21}: 0 failures
  (`fourier_check.py`, last block).
- (VERIFIED, compiled ~18:05) node B4: `sum_quadraticChar_cd_eq_zero` (p ≡ 3 mod 4),
  `card_cd_affine_of_mod_four_eq_three` (#{y² = x³ − d²x} = p), `cdCoeff_eq_LFunction`,
  `cdCoeff_prime_of_mod_four_eq_three` (a_p = 0), `normFiber_eq_empty_of_mod_four_eq_three`,
  `deuring_prime_of_mod_four_eq_three`, `deuring_prime_of_dvd` (p | d), `deuring_two`:
  DeuringCd holds at every prime n = p except the split primes p ≡ 1 (mod 4), p ∤ d.
- (VERIFIED, compiled ~18:08) `heckeEulerPoly`, `HeckeEuler d : Prop` (Euler product of
  heckeCoeff, a statement about ℤ[i] only), `map_invOfUnit_one`, `cdCoeff_prime_eq`,
  `deuringCd_of_heckeEuler` (HeckeEuler ∧ agreement at all primes → DeuringCd),
  `GaussSplit d : Prop` (agreement at split primes p ≡ 1 mod 4, p ∤ d),
  `deuringCd_of_heckeEuler_gaussSplit`, and
  `literature_hecke_fe_of_euler_gauss_fourier : (∀d, HeckeEuler d) → (∀d, GaussSplit d) →
   (∀d, CdFourier d) → HeckeContinuation5 ∧ Literature.FunctionalEquation5` (d ≡ 5 mod 8 sqfree).
  HeckeEuler/GaussSplit are implied numerically by the deuring_check data (n ≤ 400).
- (VERIFIED, compiled ~18:12) `HeckeContinuation5`, `tyzRow5b_of_readingA_five`
  (TYZThm35ReadingA ∧ HeckeContinuation5 → TYZRow5b), `heckeContinuation5_of_literature`.
- Node B1: `unitG` (unitOf in ℤ[i]), `unitOf_eq_unitG`, `unitG_mul` (by `decide`, 256 cases),
  `gmul`, `psi d p = (Np/d)·u(p)·p`, `psi_mul` (ψ_d completely multiplicative),
  `heckeCoeff_eq_sum_psi`, `psi_units` (ψ_d = 1 on ±1, ±i), `psi_unit_mul`.
- (VERIFIED, compiled ~18:25; `#print axioms` standard) node C2 except the odd Gauss sum:
  `crt_injective`, `sum_crt` (Σ_{j mod 4d} g = Σ_{a mod 4} Σ_{b mod d} g(da+4b)),
  `g2Sum`, `oddSum`, `cexp_shift`, `intCast_emod_eq`, `fourierHat_cd_eq` (ĉ_d = g2Sum · oddSum,
  d ≡ 1 mod 4), `iPow`, `cexp_two_pi_I_div_four`, `g2G`, `g2Sum_eq`, `g2G_table` (decide:
  g2G((1+i)μ) = 4(1+i)u(μ), g2G = 0 off (1+i)ℤ[i]), `OddGauss d : Prop`
  (Σ_{b∈(ℤ/d)²} (Nb/d) e(b·ν/d) = d (Nν/d)), `cdFourier_of_oddGauss`,
  `literature_hecke_fe_of_euler_gauss_oddGauss : (∀d, HeckeEuler d) → (∀d, GaussSplit d) →
   (∀d, OddGauss d) → HeckeContinuation5 ∧ Literature.FunctionalEquation5`.
- (VERIFIED, compiled ~18:20) `crt_injective2`, `sum_crt2` (coprime m, n), `oddGauss_mul`
  (OddGauss multiplicative), `oddGauss_one`, `oddGauss_of_prime` (odd squarefree d from odd primes),
  `literature_hecke_fe_of_euler_gauss_oddGaussPrime : (∀d≡5(8) sqfree, HeckeEuler d) →
   (∀ such d, GaussSplit d) → (∀ odd prime p, OddGauss p) → HeckeContinuation5 ∧ FunctionalEquation5`.
- (VERIFIED, compiled ~18:27; axioms standard) `card_cd_affine_eq` (#E_d^aff(𝔽_p) = p + Σχ),
  `sum_quadraticChar_twist`, `heckeCoeff_prime_twist`, `gaussSplit_of_one`
  (GaussSplit 1 → GaussSplit d, d ≡ 1 mod 4 odd sqfree; quadratic reciprocity),
  `literature_hecke_fe_final : (∀ d ≡ 5 (8) sqfree, HeckeEuler d) → GaussSplit 1 →
   (∀ odd prime p, OddGauss p) → HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5`.
- (VERIFIED, compiled ~18:40; axioms standard) node C2'' done: `chiC`, `gP`, `chiC_isQuadratic`,
  `chiC_ne_one`, `sum_chi_psi_mul`, `chiC_sq_of_ne_zero`, `sum_psi_sq`, `sum_psi_complete_sq`,
  `chiC_inv_eq`, `gP_sq`, `gP_ne_zero`, `gauss2D` (Σ_{x,y∈𝔽_p} χ(x²+y²)e((xn₁+yn₂)/p) = p χ(n₁²+n₂²)),
  `jacobiSym_eq_chiC`, `oddGauss_prime` (OddGauss p for odd primes p), and
  `literature_hecke_fe_of_heckeEuler_gaussSplit : (∀ d ≡ 5 (8) sqfree, HeckeEuler d) → GaussSplit 1 →
   HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5`. The Fourier side is fully proved.
- (VERIFIED numerically, `remaining_check.py` → `out_remaining_check.txt`) GaussSplit 1 at the
  29 primes p ≡ 1 (mod 4) below 300; HeckeEuler d for d ∈ {5, 13, 21, 29}, n ≤ 300: 0 failures.
- (VERIFIED, compiled ~18:47) `GaussPointCount : Prop` (pure point count on y² = x³ − x at
  p ≡ 1 mod 4, no L-function), `gaussSplit_one_of_pointCount`,
  `literature_hecke_fe_of_heckeEuler_gaussPointCount`.
- (VERIFIED, compiled ~18:55; axioms standard) B2 split: `HeckeMult d`, `HeckePrimePow d` (Props),
  `normFiber_one` (decide), `heckeCoeff_one`, `coeff_inv_quadratic`, `heckeCoeff_prime_of_dvd`,
  `heckeEuler_of_mult_primePow`, `literature_hecke_fe_of_mult_primePow_gaussPointCount :
   (∀d HeckeMult d) → (∀d HeckePrimePow d) → GaussPointCount → HeckeContinuation5 ∧ FunctionalEquation5`.
- (VERIFIED, compiled ~19:05; axioms standard) non-split prime powers: `unitOf_eq_zero_of_even`,
  `heckeCoeff_two_pow`, `heckeCoeff_pow_of_dvd`, `dvd_of_dvd_sq_add_sq` (p ≡ 3 mod 4),
  `normFiber_inert`, `heckeCoeff_inert` (h(p^{k+2}) = −p h(p^k)), `HeckePrimePowSplit d : Prop`,
  `heckePrimePow_of_split`, `literature_hecke_fe_of_mult_split_gaussPointCount :
   (∀d HeckeMult d) → (∀d HeckePrimePowSplit d) → GaussPointCount →
   HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5`.
- (VERIFIED, compiled ~19:10; axioms standard) `certifiedRankTYZClRk_of_elementary`:
  TYZThm35ReadingA → GrossZagier → (∀d HeckeMult d) → (∀d HeckePrimePowSplit d) → GaussPointCount →
  RouteK.Rank.CertifiedRankTYZClRk (CR₃ without HeckeContinuation and FunctionalEquation5).
  (MainLiterature/RankVariants not imported: their olean chain was out of date in this worktree.)
- (VERIFIED, compiled ~19:20; axioms standard) node B2a DONE: `toG`, `norm_toG`, `toG_gmul`,
  `toG_injective`, `norm_eq_one_cases`, `norm_gcd_eq` (N(gcd(γ,m)) = m for Nγ = mn coprime; Bezout),
  `unitsZ`, `conjZ`, `unitsZ_props`, `toG_conjZ`, `card_mul_fiber` (fibres of (α,β) ↦ αβ have 4
  elements), `gmul_mem_normFiber`, `heckeCoeff_zero`, `heckeMult` (HeckeMult d for all d), and
  `literature_hecke_fe_of_split_gaussPointCount : (∀ d ≡ 5 (8) sqfree, HeckePrimePowSplit d) →
   GaussPointCount → HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5`.
- (VERIFIED, compiled ~19:30; axioms standard) node B2c DONE: `isUnit_of_norm_one`,
  `prime_of_norm_prime`, `psi_split_prime` (ψ_d(p) = p), `sum_mul_bij`, `unit_mem_unitsZ`,
  `norm_unitsZ`, `psi_gmul_unit`, section Split (`split_ne`, `piZ`, `norm_piZ`, `norm_conj_piZ`,
  `not_conj_dvd`, `prime_piZ`, `prime_conj_piZ`, `p_eq_mul`, `split_dvd`, `sum_normFiber_prime`),
  `card_unitsZ`, `heckePrimePowSplit` (HeckePrimePowSplit d for all d), and
  `literature_hecke_fe_of_gaussPointCount : GaussPointCount → HeckeContinuation5 ∧
   ZInQ.Literature.FunctionalEquation5`.  The only remaining hypothesis is Gauss's point count.
- (VERIFIED, compiled ~19:35) `heckeEuler_of_odd`, `deuringCd_of_gaussPointCount`.
- (VERIFIED numerically, `gauss_jacobi_check.py`, 10 primes p ≡ 1 mod 4 ≤ 89) blueprint for
  GaussPointCount: S = Σχ₂(x³−x) = 2 Re J(χ₄, χ₂), |J|² = p, −J primary.
- (VERIFIED, compiled ~19:40) `certifiedRankTYZClRk_of_gaussPointCount : TYZThm35ReadingA →
  GrossZagier → GaussPointCount → RouteK.Rank.CertifiedRankTYZClRk`.
