/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_CategoryTheory_OverTotalPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_AffineLimit
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
-- Source-local namespace open deferred until its declaration.
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut.AlgebraicGeometry.RelPicard
open NeronModelInfra
open AlgebraicGeometry.AffineLimit

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper GeometricallyIntegral Spec Scheme SmoothProperCurve.FiniteMapData AffineLimit.specOverOfSubalgebra AffineLimit.IsLFPInj" namespace RelPicard p2m_export "AlgebraicGeometry.RelPicard" "relPicardPresheaf SubPicCondition algEquivZeroCut relSubPicPresheaf relSubPicPresheaf_map_coe isLFPInj_relPicardPresheaf" end AlgebraicGeometry.RelPicard
open scoped AlgebraicGeometry AlgebraicGeometry.RelPicard in
theorem AlgebraicGeometry.RelPicard.isLFPInj_relSubPicPresheaf_of_relPicardPresheaf
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (P : SubPicCondition c ε)
    (h : AffineLimit.IsLFPInj (relPicardPresheaf c ε)) :
    AffineLimit.IsLFPInj (relSubPicPresheaf c ε P) := by
  intro A _ _ A₀ hA₀ x₀ x₀' hx
  have hx' : (relPicardPresheaf c ε).map (AffineLimit.specOverOfSubalgebra R A₀).op x₀.1 =
      (relPicardPresheaf c ε).map (AffineLimit.specOverOfSubalgebra R A₀).op x₀'.1 := by
    have := congrArg Subtype.val hx
    simp only [relSubPicPresheaf_map_coe] at this
    exact this
  obtain ⟨A₁, hA₁, hle, h1⟩ := h A A₀ hA₀ x₀.1 x₀'.1 hx'
  refine ⟨A₁, hA₁, hle, Subtype.ext ?_⟩
  simp only [relSubPicPresheaf_map_coe] at h1
  exact h1

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m) :
    IsLFPInj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by
  obtain ⟨𝔉, -⟩ := h𝔉 0
  exact isLFPInj_relSubPicPresheaf_of_relPicardPresheaf c ε _
    (isLFPInj_relPicardPresheaf R 𝔉.twoAffineOpenCover c ε)
