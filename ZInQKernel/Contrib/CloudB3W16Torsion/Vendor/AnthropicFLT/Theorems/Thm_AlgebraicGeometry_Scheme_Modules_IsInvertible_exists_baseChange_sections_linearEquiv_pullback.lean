/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback
    {X Z : Scheme.{u}} (p : Z ⟶ X) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (U : X.Opens) (hU : IsAffineOpen U) (hpU : IsAffineOpen (p ⁻¹ᵁ U)) :
    letI := (p.app U).hom.toAlgebra
    ∃ β : Γ(Z, p ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(L, U) ≃ₗ[Γ(Z, p ⁻¹ᵁ U)] Γ((Scheme.Modules.pullback p).obj L, p ⁻¹ᵁ U),
      ∀ s : Γ(L, U), β (1 ⊗ₜ s) = (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app L).app U) s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.solution
