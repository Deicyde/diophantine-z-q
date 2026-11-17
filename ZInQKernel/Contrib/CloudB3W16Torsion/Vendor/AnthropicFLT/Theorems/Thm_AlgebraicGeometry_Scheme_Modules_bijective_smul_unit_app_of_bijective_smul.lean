/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.bijective_smul_unit_app_of_bijective_smul
    {X X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (σ : Γ(M, ⊤)) {V : X.Opens}
    (hσ : ∀ W : X.Opens, W ≤ V →
      Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ : Γ(M, W)))
    (W' : X'.Opens) (hW' : W' ≤ p ⁻¹ᵁ V) :
    Function.Bijective fun g : Γ(X', W') =>
      g • (((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op
        ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) σ) :
          Γ((Scheme.Modules.pullback p).obj M, W')) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.solution
