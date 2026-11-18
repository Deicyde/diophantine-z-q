import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinSeriesMembership
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.MixedAllLevelTrace
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinCuspDecomposition

/-!
# Genuine primitive Eisenstein membership in the mixed weight-three space

The actual primitive forms are finite constant combinations of unscaled raw
congruence forms. At weight three those raw forms equal the actual class-series
forms by their unchanged inverse-power sums. This proves membership in the
class-series span and hence in the actual mixed space, not merely in a larger
homogeneous product span. The finite interpolant inherits the same membership.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open Complex Set Matrix.SpecialLinearGroup
open scoped UpperHalfPlane BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinMixedMembership
open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinCongruenceSeries PrimitiveEisensteinGrid PrimitiveEisensteinGcdData
open PrimitiveEisensteinSeriesMembership PrimitiveEisensteinNormalization
open MixedWeightThreeAddition PrimitiveEisensteinInterpolation

/-- Actual N^-3 raw normalization agrees with the genuine class-series form. -/
theorem rawCongruenceForm_three_eq_classSeries (N : ℕ) (h3 : 3 ≤ N) (a : Fin 2 → ZMod N) :
    rawCongruenceForm N h3 3 le_rfl a =
      classSeriesForm N (by omega) (residueLift a 0) (residueLift a 1) := by
  apply DFunLike.ext
  intro τ
  rw [rawCongruenceForm_apply,unrestrictedSeries_eq_grid N (by omega),classSeriesForm_apply]
  rfl

/-- Every actual raw class form belongs to the genuine class-series span. -/
theorem rawCongruenceForm_three_mem (N : ℕ) (h3 : 3 ≤ N) (a : Fin 2 → ZMod N) :
    rawCongruenceForm N h3 3 le_rfl a ∈ classSeriesSpan N (by omega) := by
  rw [rawCongruenceForm_three_eq_classSeries]
  exact Submodule.subset_span ⟨(residueLift a 0,residueLift a 1),rfl⟩

/-- The actual unscaled primitive Eisenstein form is in the class-series span,
using the proved finite inverse coefficients, with no membership premise. -/
theorem primitive_three_mem_classSeriesSpan (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (a : Fin 2 → ZMod N) :
    ModularForm.eisensteinSeriesMF (by norm_num : (3 : ℤ) ≤ 3) a ∈ classSeriesSpan N (by omega) := by
  by_cases ha : IsCoprime (a 0) (a 1)
  · let row : PrimitiveRow N := ⟨a,ha⟩
    rw [show a = row.1 from rfl,eisensteinSeriesMF_eq_primitiveCombination N h3 3 le_rfl row]
    unfold primitiveCombinationForm
    exact Submodule.sum_mem _ (fun b _ =>
      Submodule.smul_mem _ _ (rawCongruenceForm_three_mem N h3 b.1))
  · rw [eisensteinSeriesMF_eq_zero_nonprimitive (by norm_num : (3 : ℤ) ≤ 3) a ha]
    exact Submodule.zero_mem _

/-- This inclusion is from the actual mixed-space definition. -/
theorem classSeriesSpan_le_mixedSpace (N : ℕ) (hN : 0 < N) :
    classSeriesSpan N hN ≤ MixedAllLevelTrace.mixedSpace N hN := le_sup_right

/-- Every actual primitive weight-three Eisenstein form belongs to the actual mixed space. -/
theorem primitive_three_mem_mixedSpace (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (a : Fin 2 → ZMod N) :
    ModularForm.eisensteinSeriesMF (by norm_num : (3 : ℤ) ≤ 3) a ∈ MixedAllLevelTrace.mixedSpace N (by omega) :=
  classSeriesSpan_le_mixedSpace N (by omega) (primitive_three_mem_classSeriesSpan N h3 a)

/-- The actual finite interpolant is in the class-series span, with all coefficients fixed before τ. -/
theorem interpolation_three_mem_classSeriesSpan (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (F : ModularForm (principalReal N) 3) :
    interpolation N 3 le_rfl F ∈ classSeriesSpan N (by omega) := by
  unfold interpolation
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro A _
  exact Submodule.smul_mem _ _ (primitive_three_mem_classSeriesSpan N h3 _)

/-- The actual interpolant belongs to the actual mixed space, not a substituted product space. -/
theorem interpolation_three_mem_mixedSpace (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (F : ModularForm (principalReal N) 3) :
    interpolation N 3 le_rfl F ∈ MixedAllLevelTrace.mixedSpace N (by omega) :=
  classSeriesSpan_le_mixedSpace N (by omega) (interpolation_three_mem_classSeriesSpan N h3 F)

/-- If the original actual form is mixed, its actual residual cusp is mixed as a modular form. -/
theorem residualCusp_three_mem_mixedSpace (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (F : ModularForm (principalReal N) 3) (hF : F ∈ MixedAllLevelTrace.mixedSpace N (by omega)) :
    (residualCusp N h3 3 le_rfl F : ModularForm (principalReal N) 3) ∈
      MixedAllLevelTrace.mixedSpace N (by omega) := by
  rw [residualCusp_as_modular,residualForm]
  exact Submodule.sub_mem _ hF (interpolation_three_mem_mixedSpace N h3 F)

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinMixedMembership
