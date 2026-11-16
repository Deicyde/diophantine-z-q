/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_eulerChar_tensor_lineBundle_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_eulerChar_tensor_lineBundle_eq

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

theorem solution
    {k : Type u} [Field k] {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f]
    (x : Spec (CommRingCat.of k) ⟶ S) {r : ℕ} (D : RelEffCartierDiv f r x)
    (L : (pullback f x).Modules) (hL : Scheme.Modules.IsInvertible L)
    (𝒱 : (pullback f x).TwoAffineOpenCover) :
    (Module.finrank k (𝒱.sectionsOf (pullback.snd f x) (L ⊗ D.lineBundle)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd f x) (L ⊗ D.lineBundle)).H1
      = (Module.finrank k (𝒱.sectionsOf (pullback.snd f x) L).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd f x) L).H1 + r :=
  AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq
    (pullback.snd f x) D.isInvertible_I D.isFinite D.finrank_eq L hL 𝒱
