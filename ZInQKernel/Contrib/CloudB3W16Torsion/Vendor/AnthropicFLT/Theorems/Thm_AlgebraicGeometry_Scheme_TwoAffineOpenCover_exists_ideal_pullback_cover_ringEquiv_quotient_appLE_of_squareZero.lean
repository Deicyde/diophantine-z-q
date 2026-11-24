/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥) :
    let 𝒱B := 𝒱.pullback c B
    let cB := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B)
    let 𝒱BI := 𝒱.pullback c (B ⧸ I)
    let cBI := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))
    let σst := RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))
    ∃ (J0 : Ideal (𝒱B.cover cB).A0) (J1 : Ideal (𝒱B.cover cB).A1)
      (J01 : Ideal (𝒱B.cover cB).A01),
      J0 ^ 2 = ⊥ ∧ J1 ^ 2 = ⊥ ∧ J01 ^ 2 = ⊥ ∧
      ∃ (φ0 : (𝒱B.cover cB).A0 ⧸ J0 ≃+* (𝒱BI.cover cBI).A0)
        (φ1 : (𝒱B.cover cB).A1 ⧸ J1 ≃+* (𝒱BI.cover cBI).A1)
        (φ01 : (𝒱B.cover cB).A01 ⧸ J01 ≃+* (𝒱BI.cover cBI).A01),
        (∀ a, φ01 ((Ideal.Quotient.mk J01) ((𝒱B.cover cB).ρ0 a)) =
          (𝒱BI.cover cBI).ρ0 (φ0 ((Ideal.Quotient.mk J0) a))) ∧
        (∀ a, φ01 ((Ideal.Quotient.mk J01) ((𝒱B.cover cB).ρ1 a)) =
          (𝒱BI.cover cBI).ρ1 (φ1 ((Ideal.Quotient.mk J1) a))) ∧
        (∀ a, φ0 ((Ideal.Quotient.mk J0) a) =
          (σst.appLE 𝒱B.U0 𝒱BI.U0
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a) ∧
        (∀ a, φ1 ((Ideal.Quotient.mk J1) a) =
          (σst.appLE 𝒱B.U1 𝒱BI.U1
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a) ∧
        (∀ a, φ01 ((Ideal.Quotient.mk J01) a) =
          (σst.appLE (𝒱B.U0 ⊓ 𝒱B.U1) (𝒱BI.U0 ⊓ 𝒱BI.U1)
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero.solution
