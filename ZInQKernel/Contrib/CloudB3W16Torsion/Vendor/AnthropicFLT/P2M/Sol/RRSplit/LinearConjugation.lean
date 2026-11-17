/-
CloudB3 Worker16 curve support, 2026-11-16.
Ordinary auxiliary linear-algebra proof for the Lean 4.35 source port.
This helper uses Mathlib definitions and inverse identities; it introduces no
assumed proposition, custom elaborator, syntax, notation, or runtime check.
-/
import Mathlib

namespace P2MW.CloudB3W16RRSplit

/-- Conjugating a projector transported through an inverse equivalence recovers
that projector. This is a proved cancellation identity, not a new input. -/
theorem conj_inverse_transport {K V W : Type*} [Field K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (e : V ≃ₗ[K] W) (P : W →ₗ[K] W) :
    e.conj (e.symm.toLinearMap ∘ₗ P ∘ₗ e.toLinearMap) = P := by
  apply LinearMap.ext
  intro x
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_apply_apply]

theorem conj_symm_conj {K V W : Type*} [Field K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (e : V ≃ₗ[K] W) (P : W →ₗ[K] W) : e.conj (e.symm.conj P) = P := by
  apply LinearMap.ext
  intro x
  simp only [LinearEquiv.conj_apply, LinearEquiv.symm_symm, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

end P2MW.CloudB3W16RRSplit
