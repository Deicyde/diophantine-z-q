/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite
    {k : Type u} [Field k] {Z X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (i : Z ⟶ X) (hZ : IsFinite (i ≫ x))
    (N : Z.Modules) (hN : Scheme.Modules.IsInvertible N) (𝒱 : X.TwoAffineOpenCover) :
    Module.Finite k (𝒱.sectionsOf x ((Scheme.Modules.pushforward i).obj N)).H0 ∧
      Subsingleton (𝒱.sectionsOf x ((Scheme.Modules.pushforward i).obj N)).H1 ∧
      ∀ t : Spec (CommRingCat.of k),
        Module.finrank k (𝒱.sectionsOf x ((Scheme.Modules.pushforward i).obj N)).H0 = (i ≫ x).finrank t := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite.solution
