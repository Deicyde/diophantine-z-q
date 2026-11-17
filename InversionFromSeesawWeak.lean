/-
H5 original-input Step2 / I5b interface-v2 (smoothness-free extracted group).
Copyright (c) 2026 H5 lane2 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. NEW edition, not an edit/regrade of defd0da0/077fe135
or C6 Source review008. Lead approved the v2 interface on2026-11-17T03:32Z.

Actual C3 Interfaces v2:2c3fb3623ba4a17b23e34409edcacb8500a32fbd0b461686c60f72bd0df0f44c.
ProperIntegralGroup:4010827df50f941b3f9f83e1a412d8e8c220b5426294d5d5586fe69f5faa72b1.
Only the extracted Y's I5b binder is weaker (proper+geomIntegral, no smoothness).
I5a/I0/Hbar and the ORIGINAL NOS inputs/statements are unchanged.

GM1's OUTER statement remains the true all-rational-slices/reduced-base
SeesawPulledBack. Its false one-slice openness primitive has been refuted
(Poincare on E times E) and revised by C3 in Seesaw v2 e099f159. No assembly
using that false primitive counts as reducing the goal. This ordinary arrow
still requires a real true corrected GM1 proof; no Fact/proof oracle is added.

All tensors/unit/dual/pullback/identity/inverse maps below are native and SAME
Q/group/field, symbolic u and all characteristics/dimensions. No Native,
parser/helper/AST/Root/budget/presentation/model/Source-power alias.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.Interfaces
import NativeInversionReduction
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Dual

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.InversionFromSeesawWeak

theorem inversionTranslationInvariant_of_seesaw
    (hGM1 : ZInQ.Contrib.CloudR2NOS.Step1.SeesawPulledBack.{u}) :
    ZInQ.Contrib.CloudR2NOS.Step1.InversionTranslationInvariant.{u} := by
  intro K _ _ A _ Q _ htrans
  letI : GrpObj A.X := A.grp
  haveI : IsProper A.X.hom := ZInQ.Contrib.CloudR2NOS.Step1.IsProperIntegralGroup.proper
  haveI : GeometricallyIntegral A.X.hom :=
    ZInQ.Contrib.CloudR2NOS.Step1.IsProperIntegralGroup.geomIntegral
  haveI : IsIntegral A.X.left :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.X.hom
  let f := A.X.hom
  let p1 := pullback.fst f f
  let p2 := pullback.snd f f
  let m := μ[A.X].left
  let M := (Scheme.Modules.pullback m).obj Q
  let Q1 := (Scheme.Modules.pullback p1).obj Q
  let Q2 := (Scheme.Modules.pullback p2).obj Q
  let L := M ⊗ (Scheme.Modules.pullback p1).obj Qᵛ
  let x0 := η[A.X].left
  have hx0 : x0 ≫ f = 𝟙 _ := Over.w η[A.X]
  let s0 := pullback.lift (f ≫ x0) (𝟙 A.X.left)
    (by rw [Category.assoc, hx0, Category.comp_id, Category.id_comp])
  have hs0p1 : s0 ≫ p1 = f ≫ x0 := pullback.lift_fst _ _ _
  have hs0p2 : s0 ≫ p2 = 𝟙 A.X.left := pullback.lift_snd _ _ _
  have hs0m : s0 ≫ m = 𝟙 A.X.left := by
    have h : lift (toUnit A.X ≫ η[A.X]) (𝟙 A.X) ≫ μ[A.X] = 𝟙 A.X := by
      change (1 : A.X ⟶ A.X) * (𝟙 A.X) = 𝟙 A.X
      exact one_mul _
    change (lift (toUnit A.X ≫ η[A.X]) (𝟙 A.X)).left ≫ μ[A.X].left = _
    rw [← Over.comp_left, h, Over.id_left]
  have hslices : ∀ (t : Spec (CommRingCat.of K) ⟶ A.X.left)
      (ht : t ≫ f = 𝟙 _),
      Nonempty ((Scheme.Modules.pullback
        (pullback.lift (𝟙 A.X.left) (f ≫ t)
          (by rw [Category.id_comp, Category.assoc, ht, Category.comp_id]))).obj L ≅
            Scheme.Modules.unit A.X.left) := by
    intro t ht
    let x : ZInQ.Contrib.CloudR2NOS.Step1.Pt K ⟶ A.X := Over.homMk t ht
    let st := pullback.lift (𝟙 A.X.left) (f ≫ t)
      (by rw [Category.id_comp, Category.assoc, ht, Category.comp_id])
    have hst1 : st ≫ p1 = 𝟙 A.X.left := pullback.lift_fst _ _ _
    have hstm : st ≫ m = ZInQ.Contrib.CloudR2NOS.Step1.transl A x := rfl
    obtain ⟨et⟩ := htrans x
    let em : (Scheme.Modules.pullback st).obj M ≅ Q :=
      (Scheme.Modules.pullbackComp st m).app Q ≪≫
        (Scheme.Modules.pullbackCongr hstm).app Q ≪≫ et
    let ed : (Scheme.Modules.pullback st).obj
        ((Scheme.Modules.pullback p1).obj Qᵛ) ≅ Qᵛ :=
      (Scheme.Modules.pullbackComp st p1).app Qᵛ ≪≫
        (Scheme.Modules.pullbackCongr hst1).app Qᵛ ≪≫
        (Scheme.Modules.pullbackId A.X.left).app Qᵛ
    exact ⟨Scheme.Modules.pullbackTensorObjIso st M
      ((Scheme.Modules.pullback p1).obj Qᵛ) ≪≫
        (em ⊗ᵢ ed) ≪≫ Scheme.Modules.tensorObjDualIsoUnit Q⟩
  obtain ⟨eSS⟩ := hGM1 f f x0 hx0 L hslices
  let em0 : (Scheme.Modules.pullback s0).obj M ≅ Q :=
    (Scheme.Modules.pullbackComp s0 m).app Q ≪≫
      (Scheme.Modules.pullbackCongr hs0m).app Q ≪≫
      (Scheme.Modules.pullbackId A.X.left).app Q
  obtain ⟨econst⟩ := H5OriginalDVR.Lane2.NativeCubeUnitReduction.nonempty_pullback_iso_unit_through_field_point
    f x0 Qᵛ
  let ed0 : (Scheme.Modules.pullback s0).obj
      ((Scheme.Modules.pullback p1).obj Qᵛ) ≅ Scheme.Modules.unit A.X.left :=
    (Scheme.Modules.pullbackComp s0 p1).app Qᵛ ≪≫
      (Scheme.Modules.pullbackCongr hs0p1).app Qᵛ ≪≫ econst
  let erest : (Scheme.Modules.pullback s0).obj L ≅ Q :=
    Scheme.Modules.pullbackTensorObjIso s0 M
      ((Scheme.Modules.pullback p1).obj Qᵛ) ≪≫ (em0 ⊗ᵢ ed0) ≪≫ ρ_ Q
  let eL : L ≅ Q2 := eSS ≪≫ (Scheme.Modules.pullback p2).mapIso erest
  let eD := Scheme.Modules.pullbackDualIso p1 Q
  let eL' : M ⊗ Q1ᵛ ≅ Q2 := whiskerLeftIso M eD.symm ≪≫ eL
  let eunit : Q1ᵛ ⊗ Q1 ≅ Scheme.Modules.unit A.X.left :=
    β_ Q1ᵛ Q1 ≪≫ Scheme.Modules.tensorObjDualIsoUnit Q1
  let eprod : M ≅ Q1 ⊗ Q2 :=
    (ρ_ M).symm ≪≫ whiskerLeftIso M eunit.symm ≪≫
      (α_ M Q1ᵛ Q1).symm ≪≫ whiskerRightIso eL' Q1 ≪≫ β_ Q2 Q1
  exact H5OriginalDVR.Lane2.NativeInversionReduction.inversion_tensor_iso_unit_of_actual_binary_product_iso
    A Q eprod

end H5OriginalDVR.Lane2.InversionFromSeesawWeak
