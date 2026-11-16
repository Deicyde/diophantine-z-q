/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))
    (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A'] [IsScalarTower R A₀ A'] :
    ∃ (e0 : (A' ⊗[A₀] ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A0) ≃ₐ[A']
          ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A0)
      (e1 : (A' ⊗[A₀] ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A1) ≃ₐ[A']
          ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A1)
      (e01 : (A' ⊗[A₀] ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A01) ≃ₐ[A']
          ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A01),
      (∀ s, e0 ((1 : A') ⊗ₜ[A₀] s) = ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U0)
          ((𝒱.pullback c A').U0) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) ∧
      (∀ s, e1 ((1 : A') ⊗ₜ[A₀] s) = ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U1)
          ((𝒱.pullback c A').U1) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) ∧
      (∀ s, e01 ((1 : A') ⊗ₜ[A₀] s) =
        ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1)
          ((𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.solution
