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
