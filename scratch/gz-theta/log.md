# gz-theta results log

## 2026-11-13
- 05:50 start, fresh (no earlier log). Merged origin/wip/gz-license 7f3880af (fast-forward; brings
  t25-newform, Decomposition.lean etc.).
- VERIFIED (read): leaf `ZInQ.GZDecomp.HeckeThetaNewform` in Contrib/GZDecomp/Decomp.lean.
- VERIFIED (read): TC vendored `CuspForm.twist`, `qExpansion_twist_coeff`, `twist_mem_cuspFormCharSpace`
  (Twist/Basic.lean); `Eigenform.exists_toCuspForm_eq_and_χ_eq_of_qExpansion_coeff_mul_of_prime_pow_add_two`
  (Newforms/Coefficient.lean); `restrict_mem_cuspFormCharSpace_one` (TrivialNebentypus.lean);
  `exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul` (Newforms/Decomposition.lean).
- VERIFIED (read): HeckeFE proves heckeMult, heckePrimePowSplit, heckePrimePow_of_split, heckeCoeff_one,
  heckeCoeff_zero.
- VERIFIED (searched): no theta series of Hecke characters / harmonic-polynomial theta / eta-quotient
  modularity in tc-oct16, tc-nov01, tc-main. tc-main has Hecke–Schoeneberg (GeneralLevel.lean) for even
  lattices of even rank only (reference only, not vendorable).
- Plan: docs/research/gz-theta.md §2-3. Modularity of f_1 (CMForm32) and newness (NewCM) remain Props.
- 06:10 VERIFIED (compiled): Contrib/GZTheta/Basic.lean — jacobiChar, heckeCoeff_eq_jacobiSym_mul, CMForm32,
  cmForm (twist), qExpansion_cmForm_coeff, cmForm_mem_cuspFormCharSpace (char 1), exists_eigenformAway_cmForm,
  exists_eigenform_cmForm (all T_n), NewCM, heckeThetaNewform_of_cmForm32_newCM.
- 06:25 VERIFIED (compiled): Contrib/GZTheta/BadCoeff.lean — BadCoeffCM, coeff_eq_heckeCoeff_of_good_bad,
  heckeThetaNewform_of_cmForm32_badCoeffCM (via TC Diamond–Shurman 5.8.4).
- Plan change: attack CMForm32 through the eta quotient f = η(4τ)²η(8τ)² (= f_{ψ₁}, STANDARD):
  modularity on Γ₀(32) via (i) Euclid recursion for the multiplier of η² (weight 1, no sqrt),
  (ii) Schreier generators of Γ₀(32) (Mathlib closure_mul_image_eq, SL2Z_generators) checked by decide,
  (iii) cusps via Hermite decomposition. Residual leaf would be the q-series identity
  η(4τ)²η(8τ)² = Σ heckeCoeff 1 n qⁿ (Jacobi triple product consequences; not in Mathlib/TC).
- 07:00 VERIFIED (compiled): Contrib/GZTheta/Eta.lean — eta_sq_add_intCast, eta_sq_neg_inv, etaSqExp (fuel),
  eta_sq_mobius: η((az+b)/(cz+d))² = ζ^{etaSqExp} (cz+d) η(z)², ζ = e^{πi/6}.
- 06:50 VERIFIED (compiled): Contrib/GZTheta/Eta32.lean — etaQuot32_slash_eq: η(4τ)²η(8τ)² ∣[2] γ = itself for γ ∈ Γ₀(32) (Schreier lemma, transversal R32 of 48 cosets, 96 generators, decide). Numerics: E ≡ 0 mod 12 on 3000 random γ (eta_exp_check.py); q-expansion identity η(4τ)²η(8τ)² = Σ heckeCoeff 1 n qⁿ for n ≤ 400 (qexp_check.py, 0 mismatches).
- 06:40 VERIFIED (compiled): EtaForm32.lean — exists_hermite, eta_sq_mul_smul, tendsto_eta_sq_atImInfty,
  etaQuot32_slash_isZeroAtImInfty (every cusp), etaForm32 : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2.
  Main.lean — EtaThetaIdentity (residual q-series identity), cmForm32_of_etaThetaIdentity,
  heckeThetaNewform_of_etaThetaIdentity_newCM / _badCoeffCM.
- VERIFIED: #print axioms of all main theorems = [propext, Classical.choice, Quot.sound]
  (scratch/gz-theta/Check.lean, out_check_axioms.txt).
- (Time stamps in this log before 06:40 that read 07:00 should read 06:22.)
- 07:00 VERIFIED (compiled): ThetaUnique.lean (eq_zero_of_theta_fe: entire f with θ's functional equations and ∫₀¹ f = 0 vanishes), TripleProduct.lean (jacobiTheta₂_eq_jtpP: Jacobi triple product; axioms standard).
