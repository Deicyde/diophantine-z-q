import WeightTwoPrimitiveProfiles02
import WeightTwoFiniteConvolution02

/-!
# Finite inversion bound to the actual division forms

The matrix inverted here is the concrete inverse-square unit permutation
matrix. Its image is the independently proved actual weight-two constant
profile, not an assumed profile-surjectivity statement. Fixed inverse
coefficients construct genuine finite combinations of division forms.
The constants of these forms are the signed axis deltas minus one explicit
uniform offset. No cusp decomposition or orthogonality is asserted here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable

open Complex Filter Matrix ModularForm
open UpperHalfPlane hiding I
open scoped Topology Real ModularForm MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants

open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinNormalization PrimitiveEisensteinUnitSeries

variable (N : ℕ) [NeZero N] [Fintype (PrimitiveRow N)] [DecidableEq (PrimitiveRow N)]

/-- The actual finite unit matrix at weight two. -/
def profileMatrix : Matrix (PrimitiveRow N) (PrimitiveRow N) ℂ :=
  WeightTwoFiniteConvolution.convolutionMatrix (unitPermutation N) (fun d => d.Coprime N)

/-- The independently determined principal-period finite part. -/
def profileFinitePart : ℂ := (Real.pi : ℂ) ^ 2 / (3 * (N : ℂ) ^ 2)

/-- Actual constants of the unchanged x-values on primitive residue rows. -/
def actualProfileVector : PrimitiveRow N → ℂ := fun p =>
  xConstant N ((p.1 0).val : ℤ) ((p.1 1).val : ℤ) / (N : ℂ) ^ 2

/-- The actual constants after the precisely normalized finite-part shift. -/
def shiftedProfileVector : PrimitiveRow N → ℂ := fun p =>
  actualProfileVector N p + profileFinitePart N

/-- The finite signed axis delta vector. -/
def axisVector : PrimitiveRow N → ℂ := fun p => axisProfile N p.1

/-- The genuinely proved actual profile relation for the concrete matrix. -/
theorem profileMatrix_axis (hN : 3 ≤ N) :
    (profileMatrix N).mulVec (axisVector N) = shiftedProfileVector N := by
  rw [profileMatrix, WeightTwoFiniteConvolution.convolutionMatrix_mulVec]
  funext p
  have h := primitive_xConstant_add_tail N hN p
  simpa only [axisVector, shiftedProfileVector, actualProfileVector, profileFinitePart,
    unitCoefficient, ite_mul, zero_mul] using h.symm

/-- The actual finite matrix is invertible; no profile, span, or inverse premise is supplied. -/
theorem profileMatrix_isUnit : IsUnit (profileMatrix N) :=
  WeightTwoFiniteConvolution.convolutionMatrix_isUnit (unitPermutation N) (fun d => d.Coprime N)

lemma profileMatrix_det_isUnit : IsUnit (profileMatrix N).det :=
  WeightTwoFiniteConvolution.convolutionMatrix_det_isUnit (unitPermutation N) (fun d => d.Coprime N)

/-- Ordinary inverse recovery of the actual shifted weight-two profile. -/
theorem profileMatrix_recover_shifted (hN : 3 ≤ N) :
    ((profileMatrix N)⁻¹).mulVec (shiftedProfileVector N) = axisVector N := by
  rw [← profileMatrix_axis N hN]
  exact WeightTwoFiniteConvolution.convolutionMatrix_recover (unitPermutation N)
    (fun d => d.Coprime N) (axisVector N)

/-- Literal finite inverse coefficients recover signed axis deltas from actual constants. -/
theorem axisProfile_inverse_coefficients (hN : 3 ≤ N) (p : PrimitiveRow N) :
    axisProfile N p.1 = ∑ q : PrimitiveRow N, (profileMatrix N)⁻¹ p q *
      (xConstant N ((q.1 0).val : ℤ) ((q.1 1).val : ℤ) / (N : ℂ) ^ 2 + profileFinitePart N) := by
  have h := congrFun (profileMatrix_recover_shifted N hN) p
  calc
    _ = (((profileMatrix N)⁻¹).mulVec (shiftedProfileVector N)) p := h.symm
    _ = _ := Matrix.mulVec_apply_eq_sum _ _ _

/-- The total unit weight, retaining the exact d=1 contribution. -/
def totalUnitWeight : ℂ := 1 + ∑' n : ℕ, unitCoefficient N 2 (n + 2)

lemma profileMatrix_one :
    (profileMatrix N).mulVec (fun _ : PrimitiveRow N => (1 : ℂ)) =
      fun _ => totalUnitWeight N := by
  rw [profileMatrix, WeightTwoFiniteConvolution.convolutionMatrix_mulVec]
  funext p
  simp only [unitCoefficient, mul_one, totalUnitWeight]

/-- The total scalar is nonzero by the actual finite matrix injectivity and a genuine primitive row. -/
theorem totalUnitWeight_ne_zero : totalUnitWeight N ≠ 0 := by
  intro h
  let p : PrimitiveRow N := ⟨![0, 1], ⟨0, 1, by simp⟩⟩
  have hz : (profileMatrix N).mulVec (fun _ : PrimitiveRow N => (1 : ℂ)) =
      (profileMatrix N).mulVec 0 := by
    rw [profileMatrix_one N, h, Matrix.mulVec_zero]
    rfl
  have he : (fun _ : PrimitiveRow N => (1 : ℂ)) = 0 :=
    WeightTwoFiniteConvolution.convolutionMatrix_injective (unitPermutation N)
      (fun d => d.Coprime N) hz
  exact one_ne_zero (congrFun he p)

lemma profileMatrix_row_sum (p : PrimitiveRow N) :
    (∑ q : PrimitiveRow N, profileMatrix N p q) = totalUnitWeight N := by
  simpa only [Matrix.mulVec_apply_eq_sum, mul_one] using congrFun (profileMatrix_one N) p

/-- Every row of the actual inverse has the same sum, proved without an Euler-factor guess. -/
theorem profileMatrix_inverse_row_sum (p : PrimitiveRow N) :
    (∑ q : PrimitiveRow N, (profileMatrix N)⁻¹ p q) = (totalUnitWeight N)⁻¹ := by
  have hleft : (profileMatrix N).mulVec
      (((profileMatrix N)⁻¹).mulVec (fun _ : PrimitiveRow N => (1 : ℂ))) =
      fun _ : PrimitiveRow N => (1 : ℂ) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (profileMatrix_det_isUnit N), Matrix.one_mulVec]
  have hright : (profileMatrix N).mulVec
      (fun _ : PrimitiveRow N => (totalUnitWeight N)⁻¹) = fun _ => (1 : ℂ) := by
    funext r
    rw [Matrix.mulVec_apply_eq_sum, ← Finset.sum_mul, profileMatrix_row_sum N r,
      mul_inv_cancel₀ (totalUnitWeight_ne_zero N)]
  have he : ((profileMatrix N)⁻¹).mulVec (fun _ : PrimitiveRow N => (1 : ℂ)) =
      fun _ => (totalUnitWeight N)⁻¹ :=
    WeightTwoFiniteConvolution.convolutionMatrix_injective (unitPermutation N)
      (fun d => d.Coprime N) (hleft.trans hright.symm)
  simpa only [Matrix.mulVec_apply_eq_sum, mul_one] using congrFun he p

/-- One explicit common offset for the finite division-form prototypes. -/
def uniformProfileOffset : ℂ := profileFinitePart N / totalUnitWeight N

/-- The actual period-N coefficient map, as a linear map on genuine weight-two modular forms. -/
def coefficientZeroMap (hN : 0 < N) : ModularForm (principalLevel N) 2 →ₗ[ℂ] ℂ where
  toFun f := (qExpansion (N : ℝ) f).coeff 0
  map_add' f g := by
    rw [FunLike.coe_add, ModularForm.qExpansion_add (by exact_mod_cast hN) (principalPeriod_mem N)]
    simp only [map_add]
  map_smul' a f := by
    rw [FunLike.coe_smul, ModularForm.qExpansion_smul (by exact_mod_cast hN) (principalPeriod_mem N) a f]
    simp only [PowerSeries.coeff_smul, smul_eq_mul, RingHom.id_apply]

/-- A genuine finite constant combination of the independently defined division Eisenstein forms. -/
def profileForm (hN : 0 < N) (p : PrimitiveRow N) : ModularForm (principalLevel N) 2 :=
  ∑ q : PrimitiveRow N, ((profileMatrix N)⁻¹ p q / (N : ℂ) ^ 2) •
    EisensteinWeightTwo.divisionEisensteinMF N hN ![((q.1 0).val : ℤ), ((q.1 1).val : ℤ)]

/-- The prototypes belong to the actual division-series span, not a postulated Eisenstein space. -/
theorem profileForm_mem_divisionSpan (hN : 0 < N) (p : PrimitiveRow N) :
    profileForm N hN p ∈ DivisionSeriesMembership.divisionSpan N hN := by
  apply (DivisionSeriesMembership.divisionSpan N hN).sum_mem
  intro q _
  exact (DivisionSeriesMembership.divisionSpan N hN).smul_mem _
    (DivisionSeriesMembership.divisionEisensteinMF_mem N hN ((q.1 0).val : ℤ) ((q.1 1).val : ℤ))

lemma profileForm_coeff_zero_sum (hN : 0 < N) (p : PrimitiveRow N) :
    (qExpansion (N : ℝ) (profileForm N hN p)).coeff 0 =
      ∑ q : PrimitiveRow N, ((profileMatrix N)⁻¹ p q / (N : ℂ) ^ 2) *
        xConstant N ((q.1 0).val : ℤ) ((q.1 1).val : ℤ) := by
  change coefficientZeroMap N hN (profileForm N hN p) = _
  unfold profileForm
  rw [map_sum]
  simp only [map_smul, coefficientZeroMap, LinearMap.coe_mk, AddHom.coe_mk,
    divisionEisensteinMF_coeff_zero N hN, smul_eq_mul]

/-- The actual prototypes have signed delta constants minus the explicit uniform offset. -/
theorem profileForm_coeff_zero (hN : 3 ≤ N) (p : PrimitiveRow N) :
    (qExpansion (N : ℝ) (profileForm N (by omega) p)).coeff 0 =
      axisProfile N p.1 - uniformProfileOffset N := by
  have h := axisProfile_inverse_coefficients N hN p
  have he : (∑ q : PrimitiveRow N, (profileMatrix N)⁻¹ p q *
      (xConstant N ((q.1 0).val : ℤ) ((q.1 1).val : ℤ) / (N : ℂ) ^ 2 + profileFinitePart N)) =
      (∑ q : PrimitiveRow N, ((profileMatrix N)⁻¹ p q / (N : ℂ) ^ 2) *
        xConstant N ((q.1 0).val : ℤ) ((q.1 1).val : ℤ)) +
          profileFinitePart N * (∑ q : PrimitiveRow N, (profileMatrix N)⁻¹ p q) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he, profileMatrix_inverse_row_sum N p,
    ← profileForm_coeff_zero_sum N (by omega) p] at h
  unfold uniformProfileOffset
  rw [div_eq_mul_inv]
  linear_combination -h

#print axioms profileMatrix_axis
#print axioms profileMatrix_recover_shifted
#print axioms axisProfile_inverse_coefficients
#print axioms totalUnitWeight_ne_zero
#print axioms profileMatrix_inverse_row_sum
#print axioms profileForm_mem_divisionSpan
#print axioms profileForm_coeff_zero

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants
