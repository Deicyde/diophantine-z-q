import WeightTwoAllCuspPrototypes02

/-!
# Actual prototype inclusion and boundary checks

The independently defined division form is identified with the previously
proved actual quadratic generator through its unchanged function values.
Consequently every finite prototype belongs to the good degree-two product
span. The boundary checks use the actual form coefficients at level three
and at a composite level with neither torsion coordinate a unit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open Complex Filter Matrix ModularForm
open UpperHalfPlane hiding I
open scoped Topology Real ModularForm MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants

open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinNormalization

/-- Inclusion of the unchanged actual division form in the good degree-two product span. -/
theorem divisionEisensteinMF_mem_productSpan (N : ℕ) [NeZero N] (hN : 3 ≤ N) (a b : ℤ) :
    EisensteinWeightTwo.divisionEisensteinMF N (NeZero.pos N) ![a, b] ∈
      TorsionQuadraticGenerators.productSpan N (NeZero.pos N) := by
  have he : EisensteinWeightTwo.divisionEisensteinMF N (NeZero.pos N) ![a, b] =
      TorsionQuadraticGenerators.xForm N hN a b := by
    apply DFunLike.ext
    intro τ
    rw [EisensteinWeightTwo.divisionEisensteinMF_eq_xValue_all N (NeZero.pos N)]
    exact (TorsionQuadraticGenerators.xForm_apply N hN a b τ).symm
  rw [he]
  exact TorsionQuadraticGenerators.xForm_mem_productSpan N hN a b

/-- The actual delta-profile prototypes lie in the proved good product span. -/
theorem profileForm_mem_productSpan (N : ℕ) [NeZero N]
    [Fintype (PrimitiveRow N)] [DecidableEq (PrimitiveRow N)] (hN : 3 ≤ N) (p : PrimitiveRow N) :
    profileForm N (NeZero.pos N) p ∈ TorsionQuadraticGenerators.productSpan N (NeZero.pos N) := by
  apply (TorsionQuadraticGenerators.productSpan N (NeZero.pos N)).sum_mem
  intro q _
  exact (TorsionQuadraticGenerators.productSpan N (NeZero.pos N)).smul_mem _
    (divisionEisensteinMF_mem_productSpan N hN ((q.1 0).val : ℤ) ((q.1 1).val : ℤ))

/-- The actual level-three axis coefficient, with its exact cyclotomic normalization. -/
theorem level_three_axis_check :
    (qExpansion (3 : ℝ) (EisensteinWeightTwo.divisionEisensteinMF 3 (by norm_num) ![0, 1])).coeff 0 =
      axisConstant 3 1 := by
  simpa only [Nat.cast_ofNat] using!
    (divisionEisensteinMF_coeff_zero 3 (by norm_num) 0 1).trans
      (xConstant_axis 3 0 1 (dvd_zero _) (by norm_num))

/-- A composite good row with neither coordinate a unit is not erased. -/
theorem level_six_nonunit_coordinates_check :
    (qExpansion (6 : ℝ) (EisensteinWeightTwo.divisionEisensteinMF 6 (by norm_num) ![2, 3])).coeff 0 =
      -(Real.pi : ℂ) ^ 2 / 3 := by
  simpa only [Nat.cast_ofNat] using!
    (divisionEisensteinMF_coeff_zero 6 (by norm_num) 2 3).trans
      (xConstant_nonaxis 6 2 3 (by norm_num))

/-- The actual quadratic Bernoulli coefficient at that composite row. -/
theorem level_six_mu_check :
    (qExpansion (6 : ℝ) (WeierstrassForms.muForm 6 (by norm_num) 2 3)).coeff 0 =
      (Real.pi : ℂ) ^ 2 / 9 := by
  have h := muForm_coeff_zero 6 (by norm_num) 2 3
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  norm_num [muConstant, firstRepresentative, bernoulliTwo]
  ring

/-- The bad class retains its actual zero coefficient, rather than a pole value. -/
theorem level_three_bad_check :
    (qExpansion (3 : ℝ) (EisensteinWeightTwo.divisionEisensteinMF 3 (by norm_num) ![0, 0])).coeff 0 = 0 := by
  simpa only [Nat.cast_ofNat] using!
    (divisionEisensteinMF_coeff_zero 3 (by norm_num) 0 0).trans
      (xConstant_bad 3 0 0 ⟨dvd_zero _, dvd_zero _⟩)

#print axioms divisionEisensteinMF_mem_productSpan
#print axioms profileForm_mem_productSpan
#print axioms level_three_axis_check
#print axioms level_six_nonunit_coordinates_check
#print axioms level_six_mu_check
#print axioms level_three_bad_check

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants
