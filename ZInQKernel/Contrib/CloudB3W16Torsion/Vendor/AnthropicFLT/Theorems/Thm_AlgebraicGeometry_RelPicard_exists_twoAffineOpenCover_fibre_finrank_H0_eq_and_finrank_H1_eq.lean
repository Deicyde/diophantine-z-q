/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) (K : Type u) [Field K] [Algebra k K] :
    ∃ 𝒲' : (pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)).TwoAffineOpenCover,
      ∀ (F : (pullback c t).Modules), Scheme.Modules.IsInvertible F →
        Module.finrank K (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
            (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F)).H0 =
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 ∧
        Module.finrank K (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
            (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F)).H1 =
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq.solution
