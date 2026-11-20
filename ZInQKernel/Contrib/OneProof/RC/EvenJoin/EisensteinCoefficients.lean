import ZInQKernel.Contrib.OneProof.RC.O12Eisenstein.DivisorSum
import ZInQKernel.Contrib.TauCeti.NumberTheory.MulChar.Basic
import ZInQKernel.Contrib.TauCeti.RingTheory.RootsOfUnity.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! The coefficient field of the Eisenstein columns, before proving their
holomorphic realization. The character values in the local block formula
can be placed in the same field as all of the divisor sums. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open NumberField O12Eisenstein

/-- One number field contains an ordered Dirichlet pair, its weight-two
divisor sums and every old dilation of those sums. -/
theorem exists_eisenstein_coefficient_field {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) :
    ∃ E : IntermediateField ℚ ℂ, NumberField E ∧
      (∀ a, χ₁ a ∈ E) ∧ (∀ b, χ₂ b ∈ E) ∧
      ∀ d n, degenerate d (divisorCoeff χ₁ χ₂) n ∈ E := by
  classical
  let S : Set ℂ := Set.range (fun u : (ZMod r₁)ˣ => (χ₁.toUnitHom u : ℂ)) ∪
    Set.range (fun u : (ZMod r₂)ˣ => (χ₂.toUnitHom u : ℂ))
  let : Finite S := ((Set.finite_range _).union (Set.finite_range _)).to_subtype
  have hS : ∀ x ∈ S, IsIntegral ℚ x := by
    rintro x (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · exact (χ₁.toUnitHom.isIntegral_coe_apply u).tower_top
    · exact (χ₂.toUnitHom.isIntegral_coe_apply u).tower_top
  let E := IntermediateField.adjoin ℚ S
  let : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_adjoin hS
  have hl : ∀ a, χ₁ a ∈ E := MulChar.apply_mem_of_forall_unit χ₁ E fun u => by
    rw [← MulChar.coe_toUnitHom]
    exact IntermediateField.subset_adjoin ℚ S (Or.inl ⟨u, rfl⟩)
  have hr : ∀ b, χ₂ b ∈ E := MulChar.apply_mem_of_forall_unit χ₂ E fun u => by
    rw [← MulChar.coe_toUnitHom]
    exact IntermediateField.subset_adjoin ℚ S (Or.inr ⟨u, rfl⟩)
  refine ⟨E, {}, hl, hr, fun d n => ?_⟩
  unfold degenerate
  split
  · exact sum_mem fun x _ => mul_mem (hl _) (mul_mem (hr _) (natCast_mem E _))
  · exact zero_mem E

end ZInQ.Manuscript.RC.EvenJoin
