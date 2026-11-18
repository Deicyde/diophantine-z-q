import WeightTwoAdditiveTrace02

/-!
# Actual weight-two division-prototype plus cusp decomposition

Every form is arbitrary over the complex numbers. The coefficients are its
actual constants on the complete principal quotient, fixed before the
upper-half-plane argument. The genuine division-form prototypes supply
signed delta profiles minus one uniform offset. Actual trace zero removes
that offset, and the independently proved finite kernel supplies the exact
2N normalization. The resulting residual is a genuine cusp form.

This is an additive decomposition only. No Petersson orthogonality,
uniqueness, or direct-sum assertion is made.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable

open Complex Filter Matrix ModularForm
open UpperHalfPlane hiding I
open Matrix.SpecialLinearGroup
open scoped Topology Real ModularForm MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoAdditive

open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinNormalization

/-- The actual finite primitive-row index type, with finiteness supplied by the finite residue ring. -/
@[instance_reducible]
def primitiveFintype (N : ℕ) [NeZero N] : Fintype (PrimitiveRow N) := Fintype.ofFinite _
attribute [local instance] primitiveFintype

/-- Equality on the genuine primitive-row index type. -/
@[instance_reducible]
def primitiveDecidableEq (N : ℕ) : DecidableEq (PrimitiveRow N) := Classical.decEq _
attribute [local instance] primitiveDecidableEq

/-- The signed coordinate profile is the finite weight-two kernel profile, not a weight-two primitive series. -/
lemma axisProfile_eq_constantProfile (N : ℕ) (p : Fin 2 → ZMod N) :
    WeightTwoConstants.axisProfile N p = PrimitiveEisensteinConstants.constantProfile N 2 p := by
  have hp : p = PrimitiveEisensteinConstants.positiveRow N ↔ p 0 = 0 ∧ p 1 = 1 := by
    constructor
    · intro h
      simp only [h, PrimitiveEisensteinConstants.positiveRow, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, and_self]
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i <;> simpa only [PrimitiveEisensteinConstants.positiveRow] using! (by assumption)
  have hn : p = PrimitiveEisensteinConstants.negativeRow N ↔ p 0 = 0 ∧ p 1 = -1 := by
    constructor
    · intro h
      simp only [h, PrimitiveEisensteinConstants.negativeRow, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, and_self]
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i <;> simpa only [PrimitiveEisensteinConstants.negativeRow] using! (by assumption)
  simp only [WeightTwoConstants.axisProfile, PrimitiveEisensteinConstants.constantProfile,
    hp, hn, neg_one_sq]

/-- A complete quotient class supplies a genuinely primitive row by its determinant-one bottom row. -/
def quotientPrototypeRow (N : ℕ) (A : SL(2, ZMod N)) : PrimitiveRow N :=
  ⟨PrimitiveEisensteinConstants.positiveRow N ᵥ* (A⁻¹ : SL(2, ZMod N)), by
    rw [PrimitiveEisensteinInterpolation.positive_row_action]
    exact (A⁻¹).isCoprime_row 1⟩

/-- Actual right transport of that primitive row agrees with reduction of the integral slash matrix. -/
lemma quotientPrototypeRow_action (N : ℕ) (A : SL(2, ZMod N)) (σ : SL(2, ℤ)) :
    (WeightTwoConstants.rightPrimitive N σ (quotientPrototypeRow N A)).1 =
      PrimitiveEisensteinConstants.positiveRow N ᵥ*
        (A⁻¹ * WeightTwoConstants.residueSL N σ : SL(2, ZMod N)) := by
  change (PrimitiveEisensteinConstants.positiveRow N ᵥ* (A⁻¹).1) ᵥ*
    (WeightTwoConstants.residueSL N σ).1 = _
  rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul]

/-- A genuine finite division-form combination for a complete quotient class. -/
def quotientPrototype (N : ℕ) [NeZero N] (A : SL(2, ZMod N)) :
    ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2 :=
  WeightTwoConstants.profileForm N (NeZero.pos N) (quotientPrototypeRow N A)

/-- The actual quotient prototype's complete slash constant profile. -/
theorem quotientPrototype_constantAt (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (A : SL(2, ZMod N)) (σ : SL(2, ℤ)) :
    PrimitiveEisensteinInterpolation.constantAt N 2 (quotientPrototype N A) σ =
      PrimitiveEisensteinConstants.constantProfile N 2
        (PrimitiveEisensteinConstants.positiveRow N ᵥ*
          (A⁻¹ * WeightTwoConstants.residueSL N σ : SL(2, ZMod N))) -
        WeightTwoConstants.uniformProfileOffset N := by
  change (qExpansion (N : ℝ)
    ((WeightTwoConstants.profileForm N (NeZero.pos N) (quotientPrototypeRow N A) : ℍ → ℂ)
      ∣[(2 : ℤ)] σ)).coeff 0 = _
  rw [WeightTwoConstants.profileForm_slash_coeff_zero N hN σ,
    quotientPrototypeRow_action, axisProfile_eq_constantProfile]

/-- The explicit actual 1/(2N) interpolation from complete quotient constants. -/
def divisionInterpolant (N : ℕ) [NeZero N]
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) :
    ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2 :=
  (2 * (N : ℂ))⁻¹ • ∑ A : SL(2, ZMod N),
    PrimitiveEisensteinInterpolation.finiteConstants N 2 f A • quotientPrototype N A

/-- Actual trace zero removes the offset and the actual finite kernel matches every cusp constant. -/
theorem divisionInterpolant_constantAt (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) (σ : SL(2, ℤ)) :
    PrimitiveEisensteinInterpolation.constantAt N 2 (divisionInterpolant N f) σ =
      PrimitiveEisensteinInterpolation.constantAt N 2 f σ := by
  rw [← PrimitiveEisensteinInterpolation.finiteConstants_reduce N 2 f σ]
  change PrimitiveEisensteinInterpolation.constantAtLinear N 2 σ (divisionInterpolant N f) = _
  unfold divisionInterpolant
  simp only [LinearMap.map_smul, map_sum, smul_eq_mul,
    PrimitiveEisensteinInterpolation.constantAtLinear_apply, quotientPrototype_constantAt N hN]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [finiteConstants_sum_zero N f, zero_mul, mul_zero, sub_zero]
  change (2 * (N : ℂ))⁻¹ *
    (∑ A : SL(2, ZMod N), PrimitiveEisensteinInterpolation.finiteConstants N (2 : ℤ) f A *
      PrimitiveEisensteinConstants.constantProfile N (2 : ℕ)
        (PrimitiveEisensteinConstants.positiveRow N ᵥ*
          (A⁻¹ * (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) σ) : SL(2, ZMod N)))) = _
  have hk := PrimitiveEisensteinInterpolation.actual_constant_kernel N hN 2 f
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) σ)
  have hn : 2 * (N : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N))
  calc
    _ = (2 * (N : ℂ))⁻¹ * ((2 * (N : ℂ)) *
        PrimitiveEisensteinInterpolation.finiteConstants N 2 f
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) σ)) :=
      congrArg (fun z : ℂ => (2 * (N : ℂ))⁻¹ * z) hk
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- The actual modular residual, before the cusp bundle is constructed. -/
def divisionResidual (N : ℕ) [NeZero N]
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) :
    ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2 := f - divisionInterpolant N f

/-- Every actual integral cusp-representative constant of the residual vanishes. -/
theorem divisionResidual_constantAt_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) (σ : SL(2, ℤ)) :
    PrimitiveEisensteinInterpolation.constantAt N 2 (divisionResidual N f) σ = 0 := by
  change PrimitiveEisensteinInterpolation.constantAtLinear N 2 σ (f - divisionInterpolant N f) = 0
  rw [map_sub, PrimitiveEisensteinInterpolation.constantAtLinear_apply,
    PrimitiveEisensteinInterpolation.constantAtLinear_apply, divisionInterpolant_constantAt N hN f σ,
    sub_self]

/-- The genuine cusp form retains the actual slash, holomorphy, and all-cusp vanishing fields. -/
def divisionResidualCusp (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) :
    CuspForm (PrimitiveEisensteinInterpolation.principalReal N) 2 :=
  PrimitiveEisensteinInterpolation.cuspFromConstants N 2 (divisionResidual N f)
    (divisionResidual_constantAt_zero N hN f)

lemma divisionResidualCusp_as_modular (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) :
    (divisionResidualCusp N hN f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) =
      divisionResidual N f := by
  apply DFunLike.ext
  intro τ
  rfl

/-- A closed additive division-prototype plus genuine cusp decomposition for every arbitrary form. -/
theorem actual_division_interpolant_plus_cusp (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) :
    f = divisionInterpolant N f +
      (divisionResidualCusp N hN f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) := by
  rw [divisionResidualCusp_as_modular, divisionResidual]
  abel

/-- The interpolant lies in the actual independently convergent division-series span. -/
theorem divisionInterpolant_mem_divisionSpan (N : ℕ) [NeZero N]
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) :
    divisionInterpolant N f ∈ DivisionSeriesMembership.divisionSpan N (NeZero.pos N) := by
  apply (DivisionSeriesMembership.divisionSpan N (NeZero.pos N)).smul_mem
  apply (DivisionSeriesMembership.divisionSpan N (NeZero.pos N)).sum_mem
  intro A _
  apply (DivisionSeriesMembership.divisionSpan N (NeZero.pos N)).smul_mem
  exact WeightTwoConstants.profileForm_mem_divisionSpan N (NeZero.pos N) (quotientPrototypeRow N A)

/-- The same actual interpolant lies in the proved good degree-two principal product span. -/
theorem divisionInterpolant_mem_productSpan (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) :
    divisionInterpolant N f ∈ TorsionQuadraticGenerators.productSpan N (NeZero.pos N) := by
  apply (TorsionQuadraticGenerators.productSpan N (NeZero.pos N)).smul_mem
  apply (TorsionQuadraticGenerators.productSpan N (NeZero.pos N)).sum_mem
  intro A _
  apply (TorsionQuadraticGenerators.productSpan N (NeZero.pos N)).smul_mem
  exact WeightTwoConstants.profileForm_mem_productSpan N hN (quotientPrototypeRow N A)

/-- Both actual span inclusions and the genuine cusp bundle are supplied, without a desired splitting input. -/
theorem actual_division_product_plus_cusp (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) :
    ∃ E : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2,
      E ∈ DivisionSeriesMembership.divisionSpan N (NeZero.pos N) ∧
      E ∈ TorsionQuadraticGenerators.productSpan N (NeZero.pos N) ∧
      ∃ g : CuspForm (PrimitiveEisensteinInterpolation.principalReal N) 2,
        f = E + (g : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) := by
  exact ⟨divisionInterpolant N f, divisionInterpolant_mem_divisionSpan N f,
    divisionInterpolant_mem_productSpan N hN f, divisionResidualCusp N hN f,
    actual_division_interpolant_plus_cusp N hN f⟩

/-- Explicit coefficients on the complete integral quotient, independent of the analytic argument. -/
def divisionCoefficients (N : ℕ) [NeZero N]
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2)
    (q : PrimitiveEisensteinInterpolation.principalQuotient N) : ℂ :=
  (2 * (N : ℂ))⁻¹ * PrimitiveEisensteinInterpolation.quotientConstant N 2 f q

/-- The actual interpolant is the same finite combination on every complete integral quotient class. -/
theorem divisionInterpolant_eq_complete_quotient (N : ℕ) [NeZero N]
    (f : ModularForm (PrimitiveEisensteinInterpolation.principalReal N) 2) :
    divisionInterpolant N f = ∑ q : PrimitiveEisensteinInterpolation.principalQuotient N,
      divisionCoefficients N f q •
        quotientPrototype N (PrimitiveEisensteinInterpolation.quotientReduction N q) := by
  unfold divisionInterpolant
  rw [← (PrimitiveEisensteinInterpolation.quotientReduction N).toEquiv.sum_comp
    (fun A : SL(2, ZMod N) => PrimitiveEisensteinInterpolation.finiteConstants N 2 f A • quotientPrototype N A),
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [smul_smul]
  unfold divisionCoefficients PrimitiveEisensteinInterpolation.finiteConstants
  change ((2 * (N : ℂ))⁻¹ * PrimitiveEisensteinInterpolation.quotientConstant N 2 f
    ((PrimitiveEisensteinInterpolation.quotientReduction N).symm
      (PrimitiveEisensteinInterpolation.quotientReduction N q))) • _ = _
  rw [MulEquiv.symm_apply_apply]
  rfl

#print axioms quotientPrototypeRow
#print axioms quotientPrototype_constantAt
#print axioms divisionInterpolant_constantAt
#print axioms divisionResidual_constantAt_zero
#print axioms divisionResidualCusp
#print axioms actual_division_product_plus_cusp
#print axioms divisionInterpolant_eq_complete_quotient

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoAdditive
