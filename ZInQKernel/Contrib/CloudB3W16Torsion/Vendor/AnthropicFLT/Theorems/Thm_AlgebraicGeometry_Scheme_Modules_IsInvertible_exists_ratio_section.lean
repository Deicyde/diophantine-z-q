/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ratio_section. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ratio_section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ratio_section
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s t : 𝟙_ X.Modules ⟶ M) :
    ∃ r : Γ(X, (Scheme.Modules.zeroSchemeIdeal t).support.compl),
      ∀ (U : X.affineOpens) (hU : U.1 ≤ (Scheme.Modules.zeroSchemeIdeal t).support.compl)
        (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
        (X.presheaf.map (homOfLE hU).op).hom r * Scheme.Modules.coeff t U.1 τ.hom =
          Scheme.Modules.coeff s U.1 τ.hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ratio_section.solution
