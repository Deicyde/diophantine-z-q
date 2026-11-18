import WeightTwoPrototypeProductSpan03
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinCuspDecomposition

/-!
# The actual weight-two trace constraint on the integral finite quotient

The full integral quotient is identified with the full real-image quotient
used by the ordinary modular-form trace. Its inverse representative
orientation is retained explicitly. The resulting sum of actual finite
constants vanishes for every weight-two modular form; no residue or
constant-compatibility hypothesis is supplied.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open Complex Filter Matrix ModularForm
open UpperHalfPlane hiding I
open Matrix.SpecialLinearGroup
open scoped Topology Real ModularForm MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoAdditive

open ZInQ.Contrib.HeckePrimeRationality

/-- Injectivity of the actual integral matrix embedding in the real general linear group. -/
lemma integralGL_injective : Function.Injective (mapGL ℝ : SL(2, ℤ) → GL (Fin 2) ℝ) := by
  exact toGL_injective.comp map_intCast_injective

/-- The actual integral special-linear group and its complete real image. -/
def integralRangeEquiv : SL(2, ℤ) ≃* 𝒮ℒ :=
  MulEquiv.ofBijective (mapGL ℝ).rangeRestrict ⟨by
    intro a b h
    exact integralGL_injective (congrArg Subtype.val h), by
    rintro ⟨x, γ, hγ⟩
    exact ⟨γ, Subtype.ext hγ⟩⟩

lemma integralRangeEquiv_coe (γ : SL(2, ℤ)) :
    (integralRangeEquiv γ : GL (Fin 2) ℝ) = mapGL ℝ γ := rfl

/-- Principal membership is preserved and reflected by the genuine integral embedding. -/
lemma integralRange_gamma_iff (N : ℕ) (γ : SL(2, ℤ)) :
    integralRangeEquiv γ ∈ (WeightTwoConstants.principalLevel N).subgroupOf 𝒮ℒ ↔
      γ ∈ CongruenceSubgroup.Gamma N := by
  change mapGL ℝ γ ∈ (CongruenceSubgroup.Gamma N).map (mapGL ℝ) ↔ _
  constructor
  · rintro ⟨δ, hδ, he⟩
    have h : δ = γ := integralGL_injective he
    exact h ▸ hδ
  · intro hγ
    exact Subgroup.mem_map_of_mem _ hγ

/-- The complete quotient transport, without dropping any sign or stabilizer repetitions. -/
def integralCosetEquiv (N : ℕ) : PrimitiveEisensteinInterpolation.principalQuotient N ≃
    WeightTwoConstants.principalCosets N :=
  Quotient.congr integralRangeEquiv.toEquiv (by
    intro γ δ
    change QuotientGroup.leftRel (CongruenceSubgroup.Gamma N) γ δ ↔
      QuotientGroup.leftRel ((WeightTwoConstants.principalLevel N).subgroupOf 𝒮ℒ)
        (integralRangeEquiv γ) (integralRangeEquiv δ)
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    have he : integralRangeEquiv (γ⁻¹ * δ) =
        (integralRangeEquiv γ)⁻¹ * integralRangeEquiv δ := by
      rw [map_mul, map_inv]
    rw [← he]
    exact (integralRange_gamma_iff N (γ⁻¹ * δ)).symm)

lemma integralCosetEquiv_mk (N : ℕ) (γ : SL(2, ℤ)) :
    integralCosetEquiv N (QuotientGroup.mk γ) =
      (⟦integralRangeEquiv γ⟧ : WeightTwoConstants.principalCosets N) := rfl

/-- The actual ordinary trace uses the inverse integral quotient class. -/
theorem cosetConstant_inverse_bridge (N : ℕ)
    (f : ModularForm (WeightTwoConstants.principalLevel N) 2)
    (q : PrimitiveEisensteinInterpolation.principalQuotient N) :
    WeightTwoConstants.cosetConstant N f (integralCosetEquiv N q) =
      PrimitiveEisensteinInterpolation.quotientConstant N 2 f q⁻¹ := by
  refine Quotient.inductionOn q ?_
  intro γ
  rw [integralCosetEquiv_mk, ← QuotientGroup.mk_inv,
    PrimitiveEisensteinInterpolation.quotientConstant_mk]
  unfold WeightTwoConstants.cosetConstant PrimitiveEisensteinInterpolation.constantAt
    PrimitiveEisensteinInterpolation.constantCoefficient
  rw [SlashInvariantForm.quotientFunc_mk, PrimitiveEisensteinInterpolation.slashForm_coe,
    ModularForm.SL_slash]
  have he : ((integralRangeEquiv γ) : GL (Fin 2) ℝ)⁻¹ = (mapGL ℝ) γ⁻¹ := by
    rw [integralRangeEquiv_coe, map_inv]
  rw [he]
  rfl

/-- Every arbitrary actual weight-two form has zero total constant on the full reduced finite group. -/
theorem finiteConstants_sum_zero (N : ℕ) [NeZero N]
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) :
    (∑ A : SL(2, ZMod N), PrimitiveEisensteinInterpolation.finiteConstants N 2 f A) = 0 := by
  let : Fintype (WeightTwoConstants.principalCosets N) := Fintype.ofFinite _
  have hz := WeightTwoConstants.principal_coset_constants_sum_zero N f
  calc
    _ = ∑ q : PrimitiveEisensteinInterpolation.principalQuotient N,
        PrimitiveEisensteinInterpolation.quotientConstant N 2 f q := by
      rw [← (PrimitiveEisensteinInterpolation.quotientReduction N).toEquiv.sum_comp
        (fun A : SL(2, ZMod N) => PrimitiveEisensteinInterpolation.finiteConstants N 2 f A)]
      apply Finset.sum_congr rfl
      intro q _
      unfold PrimitiveEisensteinInterpolation.finiteConstants
      change PrimitiveEisensteinInterpolation.quotientConstant N 2 f
        ((PrimitiveEisensteinInterpolation.quotientReduction N).symm
          (PrimitiveEisensteinInterpolation.quotientReduction N q)) = _
      rw [MulEquiv.symm_apply_apply]
    _ = ∑ q : PrimitiveEisensteinInterpolation.principalQuotient N,
        PrimitiveEisensteinInterpolation.quotientConstant N 2 f q⁻¹ :=
      (Equiv.sum_comp (Equiv.inv (PrimitiveEisensteinInterpolation.principalQuotient N))
        (PrimitiveEisensteinInterpolation.quotientConstant N 2 f)).symm
    _ = ∑ q : PrimitiveEisensteinInterpolation.principalQuotient N,
        WeightTwoConstants.cosetConstant N f (integralCosetEquiv N q) := by
      apply Finset.sum_congr rfl
      intro q _
      exact (cosetConstant_inverse_bridge N f q).symm
    _ = ∑ q : WeightTwoConstants.principalCosets N, WeightTwoConstants.cosetConstant N f q :=
      (integralCosetEquiv N).sum_comp (WeightTwoConstants.cosetConstant N f)
    _ = 0 := hz

#print axioms integralGL_injective
#print axioms integralCosetEquiv
#print axioms cosetConstant_inverse_bridge
#print axioms finiteConstants_sum_zero

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoAdditive
