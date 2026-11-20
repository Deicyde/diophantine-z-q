/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isOpen_setOf_subsingleton_H1_fibre. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isOpen_setOf_subsingleton_H1_fibre

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.isOpen_setOf_subsingleton_H1_fibre
    {A : Type u} [CommRing A] [IsNoetherianRing A] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A)) [IsProper c]
    (𝒱 : C.TwoAffineOpenCover) (M : C.Modules) (hM : Scheme.Modules.IsInvertible M) :
    IsOpen {𝔭 : PrimeSpectrum A | Subsingleton
      ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isOpen_setOf_subsingleton_H1_fibre.solution
