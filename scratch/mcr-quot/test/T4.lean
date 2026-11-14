import Mathlib

abbrev Qbar := AlgebraicClosure ℚ

theorem exists_algEquiv_comp_eq {K : Type} [Field K] (f1 f2 : K →+* Qbar) :
    ∃ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ k, f2 k = σ (f1 k) := by
  have : CharZero K := f1.charZero
  let _ : Algebra ℚ K := DivisionRing.toRatAlgebra
  let f1' : K →ₐ[ℚ] Qbar := f1.toRatAlgHom
  let f2' : K →ₐ[ℚ] Qbar := f2.toRatAlgHom
  let e1 := AlgEquiv.ofInjectiveField f1'
  let e2 := AlgEquiv.ofInjectiveField f2'
  let χ : f1'.fieldRange →ₐ[ℚ] f2'.fieldRange := e2.toAlgHom.comp e1.symm.toAlgHom
  refine ⟨AlgEquiv.ofBijective (χ.liftNormal Qbar)
    (Algebra.IsAlgebraic.algHom_bijective _), fun k => ?_⟩
  have h := AlgHom.liftNormal_commutes χ Qbar (e1 k)
  have h1 : algebraMap f1'.fieldRange Qbar (e1 k) = f1 k := rfl
  have h2 : χ (e1 k) = e2 k := by
    show e2 (e1.symm (e1 k)) = e2 k
    rw [AlgEquiv.symm_apply_apply]
  rw [h1, h2] at h
  exact h.symm
