import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitivePeterssonPrimitiveRows

/-!
# Actual primitive Eisenstein orthogonality at infinity

The actual gcd-one series of residue row (0,1) is reindexed by its proved
parabolic-coset equivalence. Each transported cusp seed is its actual
Eisenstein summand times the original cusp seed. The independently derived
integrable unfolding therefore gives genuine Petersson orthogonality, with
no unfolding or orthogonality premise and no factor of one half.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set UpperHalfPlane Complex Matrix Matrix.SpecialLinearGroup
open scoped Topology MatrixGroups ModularForm Pointwise ComplexConjugate

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson

lemma eisSummand_bottom_eq_denominator (k : ℤ) (γ : SL(2, ℤ)) (τ : ℍ) :
    EisensteinSeries.eisSummand k (fun i => γ 1 i) τ = (UpperHalfPlane.denom γ τ)^(-k) := by
  have hb : ![(0 : ℤ),1] ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ) = (fun i => γ 1 i) := by
    ext i
    simp [Matrix.vecMul,Fin.sum_univ_two]
    rfl
  have he := EisensteinSeries.eisSummand_SL2_apply k ![0,1] γ τ
  rw [hb] at he
  have h0 : EisensteinSeries.eisSummand k ![0,1] (γ • τ) = 1 := by
    simp [EisensteinSeries.eisSummand]
  rw [h0] at he
  have hj := zpow_ne_zero k (UpperHalfPlane.denom_ne_zero γ τ)
  have hd : EisensteinSeries.eisSummand k (fun i => γ 1 i) τ = 1 / (UpperHalfPlane.denom γ τ)^k := by
    apply (eq_div_iff hj).mpr
    rw [mul_comm]
    exact he.symm
  simpa only [one_div,_root_.zpow_neg] using hd

/-- Exact weight-k seed covariance under an actual principal-group element. -/
theorem hyperSeed_principal_summand (N k : ℕ)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ))
    (γ : CongruenceSubgroup.Gamma N) (τ : ℍ) :
    hyperSeed k f (γ • τ) = hyperSeed k f τ *
      EisensteinSeries.eisSummand (k : ℤ) (fun i => (γ : SL(2, ℤ)) 1 i) τ := by
  have hf : ⇑f ∣[(k : ℤ)] (γ : SL(2, ℤ)) = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ γ.2)
  have he := UpperHalfPlane.petersson_slash_SL (k : ℤ) f (fun _ => 1) (γ : SL(2, ℤ)) τ
  rw [hf] at he
  simp only [UpperHalfPlane.petersson,ModularForm.SL_slash_apply,one_mul,
    mul_one,zpow_natCast] at he
  rw [eisSummand_bottom_eq_denominator]
  unfold hyperSeed
  change conj (f ((γ : SL(2, ℤ)) • τ)) * ((((γ : SL(2, ℤ)) • τ).im : ℂ)^k) =
    (conj (f τ)*(τ.im : ℂ)^k) * (UpperHalfPlane.denom (γ : SL(2, ℤ)) τ)^(-(k : ℤ))
  rw [← he]
  ring

/-- The genuine periodized seed is the actual Petersson integrand, pointwise. -/
theorem periodizedSeed_eq_actual_eisenstein (N k : ℕ) [NeZero N]
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ)) (τ : ℍ) :
    (∑' q : parabolicQuotient N, periodizedSeedTerm N k f q τ) =
      UpperHalfPlane.petersson (k : ℤ) f (eisensteinSeries (infinityRow N) (k : ℤ)) τ := by
  have ht (q : parabolicQuotient N) : periodizedSeedTerm N k f q τ = hyperSeed k f τ *
      EisensteinSeries.eisSummand (k : ℤ) (primitiveRowEquiv N q).1 τ := by
    rw [periodizedSeedTerm,hyperSeed_principal_summand,primitiveRowEquiv_out]
  simp_rw [ht]
  rw [tsum_mul_left,(primitiveRowEquiv N).tsum_eq
    (fun v : infinityPrimitiveRows N => EisensteinSeries.eisSummand (k : ℤ) v.1 τ)]
  simp only [eisensteinSeries,UpperHalfPlane.petersson,hyperSeed,zpow_natCast]
  ring

lemma principalDomain_volume_lt_top (N : ℕ) [NeZero N] :
    (volume : Measure ℍ) (principalDomain N) < ⊤ := by
  have ht (q : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma N).withCenter) :
      (volume : Measure ℍ) ((q.out)⁻¹ • ModularGroup.fdo) < ⊤ := by
    rw [measure_smul]
    exact lt_of_le_of_lt (measure_mono ModularGroup.fdo_subset_fd) ModularGroup.volume_fd_lt_top
  apply lt_of_le_of_lt (measure_iUnion_le _)
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.mpr (fun q _ => ht q)

/-- The actual primitive modular-form integrand is integrable, for every row. -/
theorem primitive_pairing_integrable (N k : ℕ) [NeZero N] (hk : 3 ≤ k)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ))
    (a : Fin 2 → ZMod N) :
    IntegrableOn (UpperHalfPlane.petersson (k : ℤ) f
      (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a))
      (principalDomain N) volume := by
  let E := ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a
  change IntegrableOn (UpperHalfPlane.petersson (k : ℤ) f E) (principalDomain N) volume
  obtain ⟨C,hC⟩ := CuspFormClass.petersson_bounded_left (k : ℤ)
    ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) f E
  exact IntegrableOn.of_bound (principalDomain_volume_lt_top N)
    ((UpperHalfPlane.petersson_continuous (k : ℤ) (ModularFormClass.continuous f)
      (ModularFormClass.continuous E)).aestronglyMeasurable.restrict) C (ae_of_all _ hC)

/-- Actual primitive Eisenstein/cusp orthogonality for the infinity residue row.
All arithmetic, geometry, convergence, and cusp-zero inputs are produced. -/
theorem infinity_primitive_petersson_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ)) :
    UpperHalfPlane.peterssonInner (k : ℤ) (principalDomain N) f
      (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) (infinityRow N)) = 0 := by
  have hz := actual_domain_periodizedSeed_integral_zero N hN k hk f
  simp_rw [periodizedSeed_eq_actual_eisenstein] at hz
  exact hz

end ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson
