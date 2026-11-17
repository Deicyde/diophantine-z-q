import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinTraceOrbit
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Lower division-Eisenstein trace closure at level one

Every actual weight-two level-one modular form vanishes by the established
level-one dimension theorem. Consequently the normalized trace to level one
vanishes on every upper form, including every arbitrary series generator.
This is a base case only, not a general lower-level trace closure theorem.
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure

open EisensteinWeightTwo DivisionEisensteinLevelMaps

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The actual principal level-one group is the full modular group. -/
theorem principal_one_eq : (ΓP 1) = 𝒮ℒ := by
  rw [Gamma_one_top, Subgroup.map_top]

/-- No weight-two actual modular form survives at principal level one. -/
theorem weight_two_principal_one_zero (f : _root_.ModularForm (ΓP 1) 2) : f = 0 := by
  let hf : _root_.ModularForm 𝒮ℒ 2 := _root_.ModularForm.mcast rfl f principal_one_eq.symm
  have hzero : hf = 0 :=
    (rank_zero_iff_forall_zero.mp _root_.ModularForm.levelOne_weight_two_rank_zero) hf
  apply _root_.ModularForm.ext
  intro τ
  have he := congrArg (fun g : _root_.ModularForm 𝒮ℒ 2 => g τ) hzero
  simpa only [hf, _root_.ModularForm.mcast_apply, zero_apply] using he

/-- Actual normalized trace to level one is zero on every upper form. -/
theorem normalizedTrace_to_one_zero (M : ℕ) (hM : 0 < M)
    (f : _root_.ModularForm (ΓP M) 2) : normalizedTrace 1 M hM f = 0 :=
  weight_two_principal_one_zero _

/-- The arbitrary-label lower series-generator trace lemma is closed when N=1. -/
theorem arbitrary_generator_trace_to_one_mem (M : ℕ) (hM : 0 < M) (a : Fin 2 → ℤ) :
    normalizedTrace 1 M hM (divisionEisensteinMF M hM a) ∈ seriesSpan 1 one_pos := by
  rw [normalizedTrace_to_one_zero]
  exact Submodule.zero_mem _

/-- The whole actual upper series span descends under trace to the level-one series span. -/
theorem trace_seriesSpan_to_one (M : ℕ) (hM : 0 < M)
    (f : _root_.ModularForm (ΓP M) 2) : normalizedTrace 1 M hM f ∈ seriesSpan 1 one_pos := by
  rw [normalizedTrace_to_one_zero]
  exact Submodule.zero_mem _

/-- An upper form invariant under the full level-one group is zero. -/
theorem invariant_under_one_zero (M : ℕ) (hM : 0 < M)
    (f : _root_.ModularForm (ΓP M) 2)
    (hf : ∀ γ ∈ (ΓP 1), ⇑f ∣[(2 : ℤ)] γ = ⇑f) : f = 0 := by
  have he := restriction_normalizedTrace_of_invariant one_pos hM (one_dvd M) f hf
  rw [normalizedTrace_to_one_zero, map_zero] at he
  exact he.symm

/-- Actual invariant series-span descent to level one, with the invariant input visible. -/
theorem invariant_series_descent_to_one (M : ℕ) (hM : 0 < M)
    (f : _root_.ModularForm (ΓP M) 2)
    (hf : ∀ γ ∈ (ΓP 1), ⇑f ∣[(2 : ℤ)] γ = ⇑f) :
    ∃ g : _root_.ModularForm (ΓP 1) 2, g ∈ seriesSpan 1 one_pos ∧
      restriction 1 M (one_dvd M) g = f := by
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [map_zero, invariant_under_one_zero M hM f hf]

end ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure
