/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (L L' : X.Modules) (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.sectionsOf c L').M0)
    (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.sectionsOf c L').M1)
    (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.sectionsOf c L').M01)
    (he0 : ∀ m, e01 ((𝒱.sectionsOf c L).r0 m) = (𝒱.sectionsOf c L').r0 (e0 m))
    (he1 : ∀ m, e01 ((𝒱.sectionsOf c L).r1 m) = (𝒱.sectionsOf c L').r1 (e1 m)) :
    Nonempty (L ≅ L') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.solution
