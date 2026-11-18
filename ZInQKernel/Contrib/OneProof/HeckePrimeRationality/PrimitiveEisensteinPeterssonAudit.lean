import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinPeterssonOrthogonality

/-! Literal types and axiom audit for actual primitive Eisenstein Petersson orthogonality. -/

set_option autoImplicit false
set_option pp.universes true
open MeasureTheory UpperHalfPlane Complex Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm
open ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson

#check @horizontal
#print axioms horizontal
#check @horizontal_mean_zero
#print axioms horizontal_mean_zero
#check @horizontal_conj_mean_zero
#print axioms horizontal_conj_mean_zero
#check @horizontal_weighted_mean_zero
#print axioms horizontal_weighted_mean_zero
#check @iterated_truncated_strip_zero
#print axioms iterated_truncated_strip_zero
#check @planeSeed
#print axioms planeSeed
#check @seed_at_positive
#print axioms seed_at_positive
#check @planeSeed_continuousOn
#print axioms planeSeed_continuousOn
#check @seed_exponent_gt_neg_one
#print axioms seed_exponent_gt_neg_one
#check @seed_global_bound
#print axioms seed_global_bound
#check @cusp_uniform_exp_bound
#print axioms cusp_uniform_exp_bound
#check @seed_tail_majorant_integrable
#print axioms seed_tail_majorant_integrable
#check @vertical_majorant_integrable
#print axioms vertical_majorant_integrable
#check @planeSeed_integrable_strip
#print axioms planeSeed_integrable_strip
#check @planeSeed_strip_integral_zero
#print axioms planeSeed_strip_integral_zero
#check @coordinates
#print axioms coordinates
#check @flatVolume
#print axioms flatVolume
#check @coordinates_measurableEmbedding
#print axioms coordinates_measurableEmbedding
#check @coordinates_measurePreserving
#print axioms coordinates_measurePreserving
#check @strip
#print axioms strip
#check @strip_measurable
#print axioms strip_measurable
#check @coordinates_preimage_strip
#print axioms coordinates_preimage_strip
#check @hyperSeed
#print axioms hyperSeed
#check @density_smul_hyperSeed
#print axioms density_smul_hyperSeed
#check @flatSeed_integrable_strip
#print axioms flatSeed_integrable_strip
#check @hyperSeed_integrable_strip
#print axioms hyperSeed_integrable_strip
#check @hyperSeed_strip_integral_zero
#print axioms hyperSeed_strip_integral_zero
#check @translationGroup
#print axioms translationGroup
#check @translation_power
#print axioms translation_power
#check @translationGroup_le_principal
#print axioms translationGroup_le_principal
#check @halfOpenStrip
#print axioms halfOpenStrip
#check @halfOpenStrip_measurable
#print axioms halfOpenStrip_measurable
#check @halfOpenStrip_disjoint
#print axioms halfOpenStrip_disjoint
#check @halfOpenStrip_covers
#print axioms halfOpenStrip_covers
#check @halfOpenStrip_fundamental
#print axioms halfOpenStrip_fundamental
#check @principal_period
#print axioms principal_period
#check @hyperSeed_translation_invariant
#print axioms hyperSeed_translation_invariant
#check @hyperSeed_halfOpenStrip_zero
#print axioms hyperSeed_halfOpenStrip_zero
#check @hyperSeed_parabolic_domain_zero
#print axioms hyperSeed_parabolic_domain_zero
#check @parabolicQuotient
#print axioms parabolicQuotient
#check @parabolicTiling
#print axioms parabolicTiling
#check @periodizedSeedTerm
#print axioms periodizedSeedTerm
#check @parabolicTiling_fundamental
#print axioms parabolicTiling_fundamental
#check @parabolicTiling_measure
#print axioms parabolicTiling_measure
#check @hyperSeed_tiling_integrable_zero
#print axioms hyperSeed_tiling_integrable_zero
#check @periodizedSeed_integrable_summable
#print axioms periodizedSeed_integrable_summable
#check @periodizedSeed_integral_zero
#print axioms periodizedSeed_integral_zero
#check @principal_neg_one_not_mem
#print axioms principal_neg_one_not_mem
#check @principalPSL
#print axioms principalPSL
#check @principalToPSL
#print axioms principalToPSL
#check @principalToPSL_bijective
#print axioms principalToPSL_bijective
#check @principalDomain
#print axioms principalDomain
#check @principalDomain_fundamental
#print axioms principalDomain_fundamental
#check @actual_domain_periodizedSeed_integrable
#print axioms actual_domain_periodizedSeed_integrable
#check @actual_domain_periodizedSeed_integral_zero
#print axioms actual_domain_periodizedSeed_integral_zero
#check @infinityRow
#print axioms infinityRow
#check @infinityPrimitiveRows
#print axioms infinityPrimitiveRows
#check @principalBottomRow
#print axioms principalBottomRow
#check @principalBottomRow_surjective
#print axioms principalBottomRow_surjective
#check @same_bottom_iff_translation
#print axioms same_bottom_iff_translation
#check @quotientPrimitiveRow
#print axioms quotientPrimitiveRow
#check @quotientPrimitiveRow_mk
#print axioms quotientPrimitiveRow_mk
#check @quotientPrimitiveRow_bijective
#print axioms quotientPrimitiveRow_bijective
#check @primitiveRowEquiv
#print axioms primitiveRowEquiv
#check @primitiveRowEquiv_out
#print axioms primitiveRowEquiv_out
#check @eisSummand_bottom_eq_denominator
#print axioms eisSummand_bottom_eq_denominator
#check @hyperSeed_principal_summand
#print axioms hyperSeed_principal_summand
#check @periodizedSeed_eq_actual_eisenstein
#print axioms periodizedSeed_eq_actual_eisenstein
#check @principalDomain_volume_lt_top
#print axioms principalDomain_volume_lt_top
#check @primitive_pairing_integrable
#print axioms primitive_pairing_integrable
#check @infinity_primitive_petersson_zero
#print axioms infinity_primitive_petersson_zero
#check @principal_translate_level
#print axioms principal_translate_level
#check @principalCuspSlash
#print axioms principalCuspSlash
#check @principalCuspSlash_coe
#print axioms principalCuspSlash_coe
#check @infinity_primitive_zero_on_domain
#print axioms infinity_primitive_zero_on_domain
#check @principalDomain_translate_fundamental
#print axioms principalDomain_translate_fundamental
#check @primitive_residue_row_lift
#print axioms primitive_residue_row_lift
#check @pairing_slash_change_variables
#print axioms pairing_slash_change_variables
#check @coprime_primitive_eisenstein_petersson_zero
#print axioms coprime_primitive_eisenstein_petersson_zero
#check @actual_primitive_eisenstein_petersson_zero
#print axioms actual_primitive_eisenstein_petersson_zero
#check @actual_primitive_eisenstein_petersson_zero_left
#print axioms actual_primitive_eisenstein_petersson_zero_left
#check @actual_primitive_integrable_orthogonality
#print axioms actual_primitive_integrable_orthogonality

-- Literal actual data, domain and measure checks.
example (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) (τ : ℍ) :
    ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a τ =
      ∑' v : EisensteinSeries.gammaSet N 1 a, EisensteinSeries.eisSummand (k : ℤ) v.1 τ := rfl

example (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) 3) :
    UpperHalfPlane.peterssonInner 3 (principalDomain N) f
      (ModularForm.eisensteinSeriesMF (by norm_num : (3 : ℤ) ≤ 3) ![(-2 : ZMod N),5]) = 0 := by
  have h := actual_primitive_eisenstein_petersson_zero N hN 3 (by norm_num) ![(-2 : ZMod N),5] f
  norm_num at h
  exact h

example (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) 4) :
    IntegrableOn (UpperHalfPlane.petersson 4 f
      (ModularForm.eisensteinSeriesMF (by norm_num : (3 : ℤ) ≤ 4) (0 : Fin 2 → ZMod N)))
      (principalDomain N) volume ∧
    UpperHalfPlane.peterssonInner 4 (principalDomain N) f
      (ModularForm.eisensteinSeriesMF (by norm_num : (3 : ℤ) ≤ 4) (0 : Fin 2 → ZMod N)) = 0 := by
  have h := actual_primitive_integrable_orthogonality N hN 4 (by norm_num) 0 f
  norm_num at h
  exact h

example (N : ℕ) (hN : 3 ≤ N) :
    IsFundamentalDomain (CongruenceSubgroup.Gamma N) (principalDomain N) (volume : Measure ℍ) :=
  principalDomain_fundamental N hN

example (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ)) :
    IntegrableOn (hyperSeed k f) (halfOpenStrip N) (volume : Measure ℍ) ∧
      (∫ τ in halfOpenStrip N, hyperSeed k f τ) = 0 :=
  hyperSeed_halfOpenStrip_zero N k hk f
