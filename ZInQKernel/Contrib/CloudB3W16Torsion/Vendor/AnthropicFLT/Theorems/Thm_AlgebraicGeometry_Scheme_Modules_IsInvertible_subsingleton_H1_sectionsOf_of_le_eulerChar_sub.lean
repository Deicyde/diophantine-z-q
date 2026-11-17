/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_subsingleton_H1_sectionsOf_of_le_eulerChar_sub. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_subsingleton_H1_sectionsOf_of_le_eulerChar_sub

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.subsingleton_H1_sectionsOf_of_le_eulerChar_sub
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover)
    (h : 2 * (Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 : ℤ) - 1
        ≤ ((Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1)
          - ((Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 : ℤ)
              - Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1)) :
    Subsingleton (𝒱.sectionsOf x M).H1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_subsingleton_H1_sectionsOf_of_le_eulerChar_sub.solution
