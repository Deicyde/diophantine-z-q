/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_iff_of_isPullback
    {X T T' X₁ X₂ : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T}
    {π₁ : X₁ ⟶ T'} {g₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ T'} {g₂ : X₂ ⟶ X}
    (h₁ : IsPullback g₁ π₁ π ψ) (h₂ : IsPullback g₂ π₂ π ψ) (F : X.Modules) :
    IsIso (Scheme.Modules.baseChangeHom h₁.w F) ↔ IsIso (Scheme.Modules.baseChangeHom h₂.w F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback.solution
