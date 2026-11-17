/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_eq_of_app_eq_smul
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s₁ s₂ : 𝟙_ X.Modules ⟶ M) (u : Γ(X, ⊤)) (hu : IsUnit u)
    (h : s₂.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = u • s₁.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :
    Scheme.Modules.zeroSchemeIdeal s₁ = Scheme.Modules.zeroSchemeIdeal s₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul.solution
