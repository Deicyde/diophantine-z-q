/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

open AlgebraicCurve in

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    (h0 : Nonempty 𝒱.U0) (h1 : Nonempty 𝒱.U1)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ D : AlgebraicCurve.Divisor K X.functionField,
      Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[K]
        ↥(AlgebraicCurve.cechH0 (AlgebraicCurve.placesOf x 𝒱.U0) (AlgebraicCurve.placesOf x 𝒱.U1) D)) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[K]
        AlgebraicCurve.cechH1 (AlgebraicCurve.placesOf x 𝒱.U0) (AlgebraicCurve.placesOf x 𝒱.U1) D) := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨D, φ, hnat, hsmul, hinj, hrange, -⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x M hM
  exact ⟨D, nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn 𝒱 x h0 h1 M D φ hnat
    (fun U _ a m => hsmul U a m) hinj hrange⟩
