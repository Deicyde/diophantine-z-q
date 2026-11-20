import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Character orthogonality for the dual of the finite unit squareclass group. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenExpansion

open scoped BigOperators Classical

@[instance_reducible] def dualFintype (G : Type) [CommGroup G] [Finite G] : Fintype (G →* ℂˣ) :=
  letI := Fintype.ofFinite G
  Fintype.ofEquiv G (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some.symm.toEquiv

/-- The average of characters against a fixed character evaluation is the
indicator of the selected class. -/
theorem dual_orthogonality {G : Type} [CommGroup G] [Finite G] (a t : G) :
    letI := dualFintype G
    (Fintype.card (G →* ℂˣ) : ℂ)⁻¹ *
      (∑ χ : G →* ℂˣ, (χ t : ℂ)⁻¹ * (χ a : ℂ)) =
        if a = t then 1 else 0 := by
  classical
  letI := dualFintype G
  by_cases e : a = t
  · subst a
    have hn : (Fintype.card (G →* ℂˣ) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [Units.ne_zero, hn]
  · have he : t⁻¹ * a ≠ 1 := by
      intro h
      exact e (inv_mul_eq_one.mp h).symm
    have hsum : (∑ χ : G →* ℂˣ, (χ (t⁻¹ * a) : ℂ)) = 0 := by
      obtain ⟨ν, hν⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ he
      apply eq_zero_of_mul_eq_self_left (show (ν (t⁻¹ * a) : ℂ) ≠ 1 by
        exact fun h => hν (Units.ext h))
      simp only [Finset.mul_sum, ← Units.val_mul]
      exact Fintype.sum_bijective _ (Group.mulLeft_bijective ν) _ _ fun _ => rfl
    simpa [e, map_mul, map_inv] using
      congrArg ((Fintype.card (G →* ℂˣ) : ℂ)⁻¹ * ·) hsum


end ZInQ.Manuscript.RC.EvenExpansion
