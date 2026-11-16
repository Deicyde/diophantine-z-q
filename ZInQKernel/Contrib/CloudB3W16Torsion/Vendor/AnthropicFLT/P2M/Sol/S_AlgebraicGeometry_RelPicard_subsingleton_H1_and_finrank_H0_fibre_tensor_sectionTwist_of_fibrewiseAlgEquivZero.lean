/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open CategoryTheory.MonoidalCategory
open GoodReductionJacobian
open AlgebraicCurve

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H0 =
          r + 1 - g := by
  intro k _ s 𝒲

  have hsec : rigSection c t ε ≫ pullback.snd c t = 𝟙 _ := pullback.lift_snd _ _ _
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c t inferInstance
  have hI : (sectionIdeal c ε t).IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c t ε) hsec
  have hpow : ∀ n : ℕ, ((sectionIdeal c ε t) ^ n).IsInvertible := fun n => by
    induction n with
    | zero => rw [pow_zero, Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
    | succ n ih => rw [pow_succ]; exact ih.mul hI
  have hF : Scheme.Modules.IsInvertible (M.L ⊗ sectionTwist c ε t r) :=
    M.isInvertible.tensor (hpow r).isInvertible_invModule
  set F := M.L ⊗ sectionTwist c ε t r with hFdef

  let kb := AlgebraicClosure k
  obtain ⟨hH0, hH1⟩ :=
    Scheme.TwoAffineOpenCover.finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
      (fibreAt c t s) 𝒲 (fibreModule c t s F) (hF.pullback _).exists_trivialization kb

  let sb : Spec (CommRingCat.of kb) ⟶ T := Scheme.TwoAffineOpenCover.specMap k kb ≫ s
  let φ : pullback (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k kb) ≅
      pullback (pullback.snd c t) sb :=
    pullbackLeftPullbackSndIso (pullback.snd c t) s (Scheme.TwoAffineOpenCover.specMap k kb)
  have hφsnd : φ.inv ≫ pullback.snd (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k kb) =
      fibreAt c t sb := by
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd _ _ _).symm
  have hφfst : φ.inv ≫ (pullback.fst (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k kb) ≫
      pullback.fst (pullback.snd c t) s) = pullback.fst (pullback.snd c t) sb := by
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_fst _ _ _).symm

  let e : fibreModule c t sb F ≅ (Scheme.Modules.pullback φ.symm.hom).obj
      ((Scheme.Modules.pullback (pullback.fst (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k kb))).obj
        (fibreModule c t s F)) :=
    ((Scheme.Modules.pullback φ.inv).mapIso ((Scheme.Modules.pullbackComp _ _).app F) ≪≫
      (Scheme.Modules.pullbackComp _ _).app F ≪≫ (Scheme.Modules.pullbackCongr hφfst).app F).symm
  obtain ⟨𝒱, -, -, ⟨eH0⟩, ⟨eH1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (fibreAt c t sb)
      (pullback.snd (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k kb)) φ.symm hφsnd
      (𝒲.pullback (fibreAt c t s) kb) _ _ e

  obtain ⟨h1, h0⟩ :=
    RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed
      R c ε g hg M hM r hr kb sb 𝒱
  refine ⟨?_, ?_⟩
  · haveI : Subsingleton ((𝒲.pullback (fibreAt c t s) kb).sectionsOf
        (pullback.snd (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k kb))
        ((Scheme.Modules.pullback (pullback.fst (fibreAt c t s)
          (Scheme.TwoAffineOpenCover.specMap k kb))).obj (fibreModule c t s F))).H1 :=
      eH1.symm.toEquiv.subsingleton
    exact hH1.1 inferInstance
  · rw [← hH0, ← eH0.finrank_eq, h0]
