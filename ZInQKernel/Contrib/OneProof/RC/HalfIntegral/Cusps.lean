import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rational translations and the cusp condition

The absolute value in the tree's cusp condition allows a change of coordinates by a
positive determinant matrix without a square-root convention. This expands the
modularity claim of tex 8101–8103 (provenance (c)).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.HalfIntegral

open UpperHalfPlane Filter Function Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

/-- The determinant-one matrix for an additive translation. -/
def translateMatrix {R : Type*} [CommRing R] (t : R) : SL(2, R) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem translateMatrix_smul (t : ℚ) (z : ℍ) :
    translateMatrix t • z = (t : ℝ) +ᵥ z := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply, coe_vadd]
  simp [translateMatrix, add_comm]

private theorem rat_translate_cuspCoordinates (t : ℚ) (α : SL(2, ℤ)) :
    ∃ (β : SL(2, ℤ)) (g : GL (Fin 2) ℝ), g 1 0 = 0 ∧
      mapGL ℝ β * g = mapGL ℝ (translateMatrix t) * mapGL ℝ α := by
  let A : GL (Fin 2) ℚ := mapGL ℚ (translateMatrix t) * mapGL ℚ α
  obtain ⟨β, hβ⟩ := (A • (OnePoint.infty : OnePoint ℚ)).exists_mem_SL2 ℤ
  let G := (mapGL ℚ β)⁻¹ * A
  have hG : G 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp (by
    change ((mapGL ℚ β)⁻¹ * A) • (OnePoint.infty : OnePoint ℚ) = _
    rw [mul_smul, ← hβ, inv_smul_smul])
  refine ⟨β, G.map (algebraMap ℚ ℝ), ?_, ?_⟩
  · simp [GeneralLinearGroup.map, hG]
  · simp [G, A]

/-- Every rational translate of a function satisfying the tree's cusp condition
still satisfies that condition at every cusp. -/
theorem ratTranslate_cuspidal {k : ℕ} {f : ℍ → ℂ}
    (hf : ∀ α : SL(2, ℤ), Tendsto
      (fun z : ℍ ↦ ‖f (α • z)‖ * ‖denom (mapGL ℝ α) z‖ ^ (-(k : ℝ) / 2))
      atImInfty (𝓝 0)) (t : ℚ) (α : SL(2, ℤ)) :
    Tendsto
      (fun z : ℍ ↦ ‖f ((t : ℝ) +ᵥ (α • z))‖ * ‖denom (mapGL ℝ α) z‖ ^ (-(k : ℝ) / 2))
      atImInfty (𝓝 0) := by
  obtain ⟨β, g, hg, hβ⟩ := rat_translate_cuspCoordinates t α
  have hgdenom (z : ℍ) : denom g z = (g 1 1 : ℝ) := by simp [denom, hg]
  have htdenom (z : ℍ) : denom (mapGL ℝ (translateMatrix t)) z = 1 := by
    change (algebraMap ℚ ℝ (0 : ℚ) : ℂ) * (z : ℂ) + (algebraMap ℚ ℝ (1 : ℚ) : ℂ) = 1
    simp
  have h := ((hf β).comp (tendsto_smul_atImInfty hg)).mul_const
    (‖(g 1 1 : ℝ)‖ ^ (-(k : ℝ) / 2))
  rw [zero_mul] at h
  refine h.congr fun z ↦ ?_
  have hz : (t : ℝ) +ᵥ (α • z) = β • (g • z) := by
    rw [← translateMatrix_smul t]
    change mapGL ℝ (translateMatrix t) • (mapGL ℝ α • z) = mapGL ℝ β • (g • z)
    rw [← mul_smul, ← mul_smul, hβ]
  have hd : denom (mapGL ℝ α) z = denom (mapGL ℝ β) ((g • z : ℍ) : ℂ) * (g 1 1 : ℝ) := by
    have h₁ := denom_cocycle_σ (mapGL ℝ (translateMatrix t)) (mapGL ℝ α) z
    have h₂ := denom_cocycle_σ (mapGL ℝ β) g z
    -- The upper triangular factor has positive determinant, because all other factors have determinant one.
    have hdg : g.det = 1 := by
      have e := congrArg Matrix.GeneralLinearGroup.det hβ
      simpa using e
    rw [← hβ, htdenom, map_one, one_mul, h₂, hgdenom] at h₁
    simpa [UpperHalfPlane.σ, hdg] using h₁.symm
  simp only [Function.comp_apply, hz, hd, norm_mul, Complex.norm_real,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_assoc]

#print axioms translateMatrix_smul
#print axioms rat_translate_cuspCoordinates
#print axioms ratTranslate_cuspidal

end ZInQ.Manuscript.RC.HalfIntegral
