import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-I6-rest/SqrtChar.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-I6-rest: the group-theoretic core of B2's square-root criterion

pkg-I6 (§2, B2, glue item 2): "a character of a profinite abelian group `Γ` is a square iff it
kills `Γ[2]`".  For characters with values in `ℚ/ℤ` (written additively; finite-order characters
of a profinite group take values in `μ_∞ ≅ ℚ/ℤ`) and any abelian group `Γ`, this is proved here
from the divisibility (Baer injectivity) of `ℚ/ℤ`, Mathlib's
`CharacterModule.dual_surjective_of_injective`.  Applied to a finite quotient `Γ` of `G_{ℚ_p}^{ab}`
through which `χ` factors, it gives a square root on `Γ`, hence a continuous one on `G_{ℚ_p}`.
-/

namespace GlueI6Rest

/-- `χ : Γ → ℚ/ℤ` is twice a character iff `χ` vanishes on the `2`-torsion `Γ[2]`. -/
theorem exists_half_iff {Γ : Type} [AddCommGroup Γ] (χ : Γ →+ AddCircle (1 : ℚ)) :
    (∃ ψ : Γ →+ AddCircle (1 : ℚ), ∀ g, 2 • ψ g = χ g) ↔ ∀ g : Γ, 2 • g = 0 → χ g = 0 := by
  constructor
  · rintro ⟨ψ, hψ⟩ g hg
    rw [← hψ, ← map_nsmul, hg, map_zero]
  · intro h
    let d : Γ →+ Γ :=
      { toFun := fun g => 2 • g, map_zero' := smul_zero 2, map_add' := fun a b => smul_add 2 a b }
    have hker : d.ker ≤ χ.ker := fun g hg => h g (AddMonoidHom.mem_ker.mp hg)
    let χq := QuotientAddGroup.lift d.ker χ hker
    let e := QuotientAddGroup.quotientKerEquivRange d
    let χr : d.range →+ AddCircle (1 : ℚ) := χq.comp e.symm.toAddMonoidHom
    obtain ⟨ψ, hψ⟩ := CharacterModule.dual_surjective_of_injective (R := ℤ)
      d.range.subtype.toIntLinearMap Subtype.val_injective χr
    refine ⟨ψ, fun g => ?_⟩
    have hm : d g ∈ d.range := AddMonoidHom.mem_range.mpr ⟨g, rfl⟩
    have h1 := DFunLike.congr_fun hψ ⟨d g, hm⟩
    have h2 : e.symm ⟨d g, hm⟩ = (g : Γ ⧸ d.ker) := by
      rw [AddEquiv.symm_apply_eq]; rfl
    calc 2 • ψ g = ψ (d g) := (map_nsmul ψ 2 g).symm
      _ = χr ⟨d g, hm⟩ := h1
      _ = χ g := by
        simp only [χr, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h2, χq,
          QuotientAddGroup.lift_mk]

end GlueI6Rest

