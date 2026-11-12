import Mathlib

open NumberField
open scoped Pointwise

namespace GlueConj

abbrev GQ := Field.absoluteGaloisGroup ℚ
abbrev Qbar := AlgebraicClosure ℚ

instance : IsGalois ℚ (AlgebraicClosure ℚ) := {}

/-- `G_ℚ` as the type of `ℚ`-automorphisms of `ℚ̄` (definitionally `Gal`). -/
abbrev Gal := Qbar ≃ₐ[ℚ] Qbar

/-- The algebraic integers `B ⊆ ℚ̄`. -/
noncomputable abbrev B := integralClosure ℤ Qbar

theorem isIntegral_smul (σ : Gal) (b : B) : IsIntegral ℤ (σ (b : Qbar)) :=
  (mem_integralClosure_iff ℤ Qbar).mp b.2 |>.map ((σ : Qbar →+* Qbar).toIntAlgHom)

noncomputable instance : MulSemiringAction Gal B where
  smul σ b := ⟨σ b, isIntegral_smul σ b⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl
  smul_zero σ := Subtype.ext (map_zero σ)
  smul_add σ _ _ := Subtype.ext (map_add σ _ _)
  smul_one σ := Subtype.ext (map_one σ)
  smul_mul σ _ _ := Subtype.ext (map_mul σ _ _)

@[simp] theorem coe_smul (σ : Gal) (b : B) : ((σ • b : B) : Qbar) = σ (b : Qbar) := rfl

instance : SMulCommClass Gal ℤ B := inferInstance

instance : Algebra.IsInvariant ℤ B Gal := by
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ σ : Gal, σ (b : Qbar) = b := fun σ => congrArg Subtype.val (hb σ)
  have hbot : (b : Qbar) ∈ (⊥ : IntermediateField ℚ Qbar) :=
    (InfiniteGalois.mem_bot_iff_fixed (b : Qbar)).mpr hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
  have hint : IsIntegral ℤ (algebraMap ℚ Qbar q) := by
    rw [hq]; exact (mem_integralClosure_iff ℤ Qbar).mp b.2
  rw [isIntegral_algebraMap_iff] at hint
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨n, Subtype.ext ?_⟩
  rw [← hq]; simp

noncomputable instance : TopologicalSpace B := ⊥
instance : DiscreteTopology B := ⟨rfl⟩

instance : ContinuousSMul Gal B := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro b
  convert stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Qbar) (b : Qbar) using 2
  ext σ
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

/-- Transitivity on primes of `B` over the same prime of `ℤ` (Mathlib, profinite case). -/
theorem exists_smul_eq (P Q : Ideal B) [P.IsPrime] [Q.IsPrime] (h : P.under ℤ = Q.under ℤ) :
    ∃ g : Gal, Q = g • P :=
  Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := ℤ) (G := Gal) P Q h

end GlueConj
