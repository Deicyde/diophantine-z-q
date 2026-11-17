/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_exists_finiteMapData_le_isUnit_of_twoAffineOpenCover. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoChartPoleDatum_transcendental_le_isUnit_of_twoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart_right
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_levelSet_free_of_twoChartPoleDatum
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_finiteMapData_le_isUnit_of_twoAffineOpenCover

set_option autoImplicit false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝒱 : C.TwoAffineOpenCover) (m₀ : ℕ) :
    ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ IsUnit (𝔉.m : R) := by
  obtain ⟨U, V, hcov, hUε, f, g, hf, hg, hfg, m, hm₀, hunit, ⟨hfree, hrank⟩, hftU, hftV⟩ :=
    AlgebraicGeometry.SmoothProperCurve.exists_twoChartPoleDatum_transcendental_le_isUnit_of_twoAffineOpenCover
      R c ε 𝒱 m₀
  obtain ⟨hU, hfin⟩ :=
    AlgebraicGeometry.Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart c U V f g hcov hg hfg hftU
  obtain ⟨hV, hfinV⟩ :=
    AlgebraicGeometry.Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart_right c U V f g hcov hf hfg hftV
  exact ⟨{ U := U, V := V, f := f, g := g, m := m
           isAffineOpen_U := hU, isAffineOpen_V := hV, sup_eq_top := hcov, mem_U_iff := hUε
           inf_eq_basicOpen := hf, inf_eq_basicOpen_g := hg, res_f_mul_res_g := hfg
           finite_f := hfin, finite_g := hfinV
           levelSet_free :=
             AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum R c ε U V hU hV hcov hUε
               f g hf hg hfg m hfree hrank hfin hfinV }, hm₀, hunit⟩
