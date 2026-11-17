/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_isLFPSurj_relPicardPresheaf. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_AffineLimit
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isLFPSurj_relPicardPresheaf

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    AffineLimit.IsLFPSurj (relPicardPresheaf c ε) := by
  intro A _ _ x
  induction x using Quotient.inductionOn with
  | h M =>
  obtain ⟨A₀, hA₀, M₀, hiso⟩ := AlgebraicGeometry.RelPicard.LFP.exists_fg_nonempty_iso_pullbackAlong R 𝒱 c ε A M
  exact ⟨A₀, hA₀, Quotient.mk _ M₀, Quotient.sound hiso⟩
