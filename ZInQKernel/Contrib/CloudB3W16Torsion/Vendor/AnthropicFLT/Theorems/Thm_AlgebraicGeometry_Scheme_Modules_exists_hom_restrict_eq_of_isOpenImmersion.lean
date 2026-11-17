/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_hom_restrict_eq_of_isOpenImmersion
    {X Y₀ Y₁ Y₀₁ : Scheme.{u}} (f₀ : Y₀ ⟶ X) (f₁ : Y₁ ⟶ X) [IsOpenImmersion f₀] [IsOpenImmersion f₁]
    (g₀ : Y₀₁ ⟶ Y₀) (g₁ : Y₀₁ ⟶ Y₁) [IsOpenImmersion g₀] [IsOpenImmersion g₁]
    (hg : g₀ ≫ f₀ = g₁ ≫ f₁) (hcov : f₀.opensRange ⊔ f₁.opensRange = ⊤)
    (hov : f₀.opensRange ⊓ f₁.opensRange ≤ (g₀ ≫ f₀).opensRange)
    {M N : X.Modules} (ψ₀ : M.restrict f₀ ⟶ N.restrict f₀) (ψ₁ : M.restrict f₁ ⟶ N.restrict f₁)
    (hψ : (Scheme.Modules.restrictFunctorComp g₀ f₀).hom.app M ≫ (Scheme.Modules.restrictFunctor g₀).map ψ₀ ≫
            (Scheme.Modules.restrictFunctorComp g₀ f₀).inv.app N =
          (Scheme.Modules.restrictFunctorCongr hg).hom.app M ≫
            (Scheme.Modules.restrictFunctorComp g₁ f₁).hom.app M ≫ (Scheme.Modules.restrictFunctor g₁).map ψ₁ ≫
            (Scheme.Modules.restrictFunctorComp g₁ f₁).inv.app N ≫ (Scheme.Modules.restrictFunctorCongr hg).inv.app N) :
    ∃ φ : M ⟶ N, (Scheme.Modules.restrictFunctor f₀).map φ = ψ₀ ∧ (Scheme.Modules.restrictFunctor f₁).map φ = ψ₁ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion.solution
