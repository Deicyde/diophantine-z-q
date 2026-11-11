# redei-fp log

## Step 1: Redei/Field.lean — DONE (compiles with `lake env lean`)
- card_gal, omega_sq, isIntegral_omega, omegaO (+ simp lemmas), omegaO_sq, theta_eq, isIntegral_theta,
  thetaO, two_mul_thetaO, conj_omega, conj_apply (σ = star), conj_unique, conj_conj, conj_mul_self,
  eq_one_or_eq_conj, exists_conj_ne_one, algebraMap_smul, conj_omegaO, algNorm_eq, norm_eq_mul_conj,
  norm_nonneg, algNorm_coe, normZ_nonneg, normZ_eq_mul_conj, finrank_int, normZ_intCast, normZ_natCast,
  normZ_omega, exists_int_of_coe_eq_algebraMap (O ∩ ℚ = ℤ), intCast_injective, intCast_dvd_intCast_iff,
  isUnit_intCast_iff, rat_unit_eq, natCast_dvd_natCast_iff, span_natCast_eq_span_natCast_iff.
- Fixes: `ext` on 𝓞 K descends into re/im → use `apply RingOfIntegers.ext`; `AlgEquiv.ext fun x => _`;
  map_smul for AlgEquiv failed (MulActionHomClass) → Algebra.smul_def + AlgEquiv.commutes;
  re_one/im_one are scoped simp lemmas → pass explicitly.
