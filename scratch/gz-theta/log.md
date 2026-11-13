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
