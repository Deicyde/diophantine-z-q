/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat

set_option backward.isDefEq.respectTransparency false

universe u

set_option autoImplicit false

open TensorProduct

theorem Module.Projective.exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P₁ P₂ : Type u) [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₁] [Module R P₂]
    [Module.Projective R P₁] [Module.Finite R P₁]
    [Module.Projective R P₂] [Module.Finite R P₂]
    (e : ((R ⧸ I) ⊗[R] P₁) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] P₂)) :
    ∃ σ' : P₁ ≃ₗ[R] P₂, ∀ p : P₁, (1 : R ⧸ I) ⊗ₜ[R] σ' p = e ((1 : R ⧸ I) ⊗ₜ[R] p) := by p2m_exact_reverting @_root_.P2MW.S_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat.solution
