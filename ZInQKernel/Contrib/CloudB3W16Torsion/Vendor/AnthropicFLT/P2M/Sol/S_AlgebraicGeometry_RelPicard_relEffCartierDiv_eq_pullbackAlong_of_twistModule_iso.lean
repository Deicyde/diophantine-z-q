/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesRigidify
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H0_fibre_eq_one_of_subsingleton_H1
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso

set_option autoImplicit false

universe u

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec Scheme IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Modules Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelPicard.baseChangeSnd Scheme.Modules.fltDual Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv RelEffCartierDiv.ext RelEffCartierDiv.pullbackAlong_comp SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover RelEffCartierDiv.twistModule_def Scheme.Modules.rigidify Scheme.Modules.rigidify_def Scheme.Modules.rigidifyMapIso Scheme.Modules.tensorTensorTensorComm Scheme.Modules.pullbackTensorObjIsoFLT Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsCartierFLT.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsCartierFLT Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.Modules.IsInvertible.nonempty_rigidify_pullback_tensor_iso RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback Scheme.IdealSheafData.comap_mulFLT)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd rigSection RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionIdeal sectionTwist fibreModule rigSection_snd RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre finrank_H0_fibre_eq_one_of_subsingleton_H1 nonempty_pullback_sectionTwist_iso)
namespace K5bSupply
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso.AlgebraicGeometry.RelPicard
open NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem isInvertible_sectionIdeal {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (sectionIdeal c ε u).IsCartierFLT :=
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c u) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c u inferInstance
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c u) (rigSection c u ε) (rigSection_snd ε u)

theorem isInvertible_sectionTwist {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    Scheme.Modules.IsInvertible (sectionTwist c ε u n) :=
  ((isInvertible_sectionIdeal R c ε u).pow n).isInvertible_invModule

theorem isInvertible_Mγ {e n : ℕ} {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R))
    (LV : RigidifiedLineBundle c ε u) (DγV : RelEffCartierDiv c e u) :
    Scheme.Modules.IsInvertible (LV.L ⊗ (sectionTwist c ε u n ⊗ DγV.idealModule)) :=
  LV.isInvertible.tensor ((isInvertible_sectionTwist R c ε u n).tensor DγV.isInvertible_I.isInvertible_module)

theorem nonempty_twistModule_iso
    {g e : ℕ} {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R))
    (LU : RigidifiedLineBundle c ε u) (DγU : RelEffCartierDiv c e u)
    (D₀ : RelEffCartierDiv c g u) (D : RelEffCartierDiv c (g + e) u) (hD : D.I = D₀.I * DγU.I)
    (N : V.Modules) (hN : Scheme.Modules.IsInvertible N)
    (e₀ : D₀.lineBundle ≅ (LU.L ⊗ (sectionTwist c ε u (g + e) ⊗ DγU.idealModule)) ⊗
      (Scheme.Modules.pullback (pullback.snd c u)).obj N) :
    Nonempty (D.twistModule c ε ≅ LU.L) := by
  have hsIr : ((sectionIdeal c ε u) ^ (g + e)).IsCartierFLT := (isInvertible_sectionIdeal R c ε u).pow _
  have hD₀ : D₀.I.IsCartierFLT := D₀.isInvertible_I
  have hDγ : DγU.I.IsCartierFLT := DγU.isInvertible_I
  have i1 : D.lineBundle ≅ D₀.lineBundle ⊗ DγU.lineBundle :=
    eqToIso (congrArg Scheme.IdealSheafData.invModule hD) ≪≫ (hD₀.nonempty_mul_invModule_iso_tensor hDγ).some
  have cST : sectionTwist c ε u (g + e) ⊗ ((sectionIdeal c ε u) ^ (g + e)).module ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ (hsIr.isInvertible_module.dual).2.some
  have cγ : DγU.lineBundle ⊗ DγU.idealModule ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ (hDγ.isInvertible_module.dual).2.some
  have i3 : (((LU.L ⊗ (sectionTwist c ε u (g + e) ⊗ DγU.idealModule)) ⊗
      (Scheme.Modules.pullback (pullback.snd c u)).obj N) ⊗ DγU.lineBundle) ⊗
        ((sectionIdeal c ε u) ^ (g + e)).module ≅
      (Scheme.Modules.pullback (pullback.snd c u)).obj N ⊗ LU.L :=
    (α_ _ _ _) ≪≫ ((β_ _ _) ⊗ᵢ (β_ _ _)) ≪≫ (α_ _ _ _) ≪≫
      (Iso.refl _ ⊗ᵢ ((α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ
        (Scheme.Modules.tensorTensorTensorComm _ _ _ _ ≪≫ (cST ⊗ᵢ ((β_ _ _) ≪≫ cγ)) ≪≫ (λ_ _))) ≪≫ (ρ_ _)))
  have i4 : D.lineBundle ⊗ ((sectionIdeal c ε u) ^ (g + e)).module ≅
      (Scheme.Modules.pullback (pullback.snd c u)).obj N ⊗ LU.L :=
    ((i1 ≪≫ (e₀ ⊗ᵢ Iso.refl _)) ⊗ᵢ Iso.refl _) ≪≫ i3
  have i5 : Scheme.Modules.rigidify (rigSection c u ε) (pullback.snd c u) LU.L ≅ LU.L :=
    (RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified LU).some
  rw [RelEffCartierDiv.twistModule_def]
  exact ⟨Scheme.Modules.rigidifyMapIso _ _ i4 ≪≫
    (Scheme.Modules.IsInvertible.nonempty_rigidify_pullback_tensor_iso (rigSection_snd ε u) hN LU.isInvertible).some ≪≫
    i5⟩

theorem exists_lineBundle_iso_of_twistModule_iso
    {g e : ℕ} {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R))
    (LU : RigidifiedLineBundle c ε u) (DγU : RelEffCartierDiv c e u)
    (D₀ : RelEffCartierDiv c g u) (D : RelEffCartierDiv c (g + e) u) (hD : D.I = D₀.I * DγU.I)
    (hDL : Nonempty (D.twistModule c ε ≅ LU.L)) :
    ∃ N : V.Modules, Scheme.Modules.IsInvertible N ∧
      Nonempty (D₀.lineBundle ≅ (LU.L ⊗ (sectionTwist c ε u (g + e) ⊗ DγU.idealModule)) ⊗
        (Scheme.Modules.pullback (pullback.snd c u)).obj N) := by
  have hsIr : ((sectionIdeal c ε u) ^ (g + e)).IsCartierFLT := (isInvertible_sectionIdeal R c ε u).pow _
  have hD₀ : D₀.I.IsCartierFLT := D₀.isInvertible_I
  have hDγ : DγU.I.IsCartierFLT := DγU.isInvertible_I
  have hDI : D.I.IsCartierFLT := D.isInvertible_I

  set F := ((sectionIdeal c ε u) ^ (g + e)).module with hF
  set X := D.lineBundle ⊗ F with hX
  have hXinv : Scheme.Modules.IsInvertible X := hDI.isInvertible_invModule.tensor hsIr.isInvertible_module
  set N₀ : V.Modules := Scheme.Modules.fltDual ((Scheme.Modules.pullback (rigSection c u ε)).obj X) with hN₀
  have hN₀ : Scheme.Modules.IsInvertible N₀ := (hXinv.pullback _).dual.1

  refine ⟨Scheme.Modules.fltDual N₀, hN₀.dual.1, ?_⟩
  have cN : (Scheme.Modules.pullback (pullback.snd c u)).obj N₀ ⊗
      (Scheme.Modules.pullback (pullback.snd c u)).obj (Scheme.Modules.fltDual N₀) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackTensorObjIsoFLT (pullback.snd c u) _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso hN₀.dual.2.some ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _

  have j0 : X ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N₀ ≅ LU.L := by
    have h := hDL.some
    rw [RelEffCartierDiv.twistModule_def, Scheme.Modules.rigidify_def] at h
    exact h

  have j1 : X ≅ LU.L ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj (Scheme.Modules.fltDual N₀) :=
    (ρ_ X).symm ≪≫ (Iso.refl X ⊗ᵢ cN.symm) ≪≫ (α_ _ _ _).symm ≪≫ (j0 ⊗ᵢ Iso.refl _)

  have cST : F ⊗ sectionTwist c ε u (g + e) ≅ 𝟙_ _ := by
    rw [hF]; exact (hsIr.isInvertible_module.dual).2.some
  have cγ : DγU.lineBundle ⊗ DγU.idealModule ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ (hDγ.isInvertible_module.dual).2.some

  have j2 : D.lineBundle ≅ (LU.L ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj (Scheme.Modules.fltDual N₀)) ⊗
      sectionTwist c ε u (g + e) :=
    (ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ cST.symm) ≪≫ (α_ _ _ _).symm ≪≫ ((show D.lineBundle ⊗ F ≅ _ from j1) ⊗ᵢ Iso.refl _)

  have i1 : D.lineBundle ≅ D₀.lineBundle ⊗ DγU.lineBundle :=
    eqToIso (congrArg Scheme.IdealSheafData.invModule hD) ≪≫ (hD₀.nonempty_mul_invModule_iso_tensor hDγ).some
  have j3 : D₀.lineBundle ≅ D.lineBundle ⊗ DγU.idealModule :=
    (ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ cγ.symm) ≪≫ (α_ _ _ _).symm ≪≫ (i1.symm ⊗ᵢ Iso.refl _)
  refine ⟨j3 ≪≫ (j2 ⊗ᵢ Iso.refl _) ≪≫ ?_⟩

  exact (α_ _ _ _) ≪≫ (α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ (β_ _ _)) ≪≫ (α_ _ _ _).symm

section Transport

variable {e : ℕ} (r : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
  {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ1 : T' ⟶ T) (L : RigidifiedLineBundle c ε t)
  {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')

noncomputable def fibreIso : pullback (pullback.snd c t) (s' ≫ ψ1) ≅ pullback (pullback.snd c (ψ1 ≫ t)) s' :=
  pullbackLeftPullbackSndIso c t (s' ≫ ψ1) ≪≫ pullback.congrHom rfl (Category.assoc s' ψ1 t) ≪≫
    (pullbackLeftPullbackSndIso c (ψ1 ≫ t) s').symm

theorem fibreIso_hom_fibreAt :
    (fibreIso R c t ψ1 s').hom ≫ fibreAt c (ψ1 ≫ t) s' = fibreAt c t (s' ≫ ψ1) := by
  simp only [fibreIso, fibreAt, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

theorem fibreIso_hom_fst_baseChangeSnd :
    (fibreIso R c t ψ1 s').hom ≫ pullback.fst (pullback.snd c (ψ1 ≫ t)) s' ≫
        baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t) =
      pullback.fst (pullback.snd c t) (s' ≫ ψ1) := by
  have hβ : baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t) =
      pullback.lift (pullback.fst c (ψ1 ≫ t) ≫ 𝟙 C) (pullback.snd c (ψ1 ≫ t) ≫ ψ1) (by simp [pullback.condition]) := rfl
  rw [hβ]
  apply pullback.hom_ext
  · simp only [fibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_fst, Category.comp_id,
      pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullbackLeftPullbackSndIso_hom_fst]
  · simp only [fibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      pullbackLeftPullbackSndIso_inv_fst_snd_assoc, pullback.congrHom_hom,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

theorem nonempty_Mγ_iso_pullback :
    Nonempty ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
        (sectionTwist c ε (ψ1 ≫ t) r ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule) ≅
      (Scheme.Modules.pullback (baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t))).obj
        (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))) := by
  let ψ : SchemeHomOver (ψ1 ≫ t) t := ⟨ψ1, rfl⟩
  have hcomp : (Dγ.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ1 ψ.2 =
      Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _) :=
    RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _
  have hI : (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).I =
      (Dγ.pullbackAlong t (Category.comp_id t)).I.comap (baseChangeSnd c ψ) := by
    rw [← hcomp]; rfl
  have iγ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (Dγ.pullbackAlong t (Category.comp_id t)).idealModule ≅
      (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule := by
    haveI := Scheme.IdealSheafData.IsCartierFLT.isIso_pullbackModuleComparison (baseChangeSnd c ψ)
      (Dγ.pullbackAlong t (Category.comp_id t)).isInvertible_I
      (hI ▸ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).isInvertible_I)
    exact asIso ((Dγ.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison (baseChangeSnd c ψ)) ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hI).symm
  exact ⟨(Iso.refl _ ⊗ᵢ ((nonempty_pullback_sectionTwist_iso R c ε ψ r).some.symm ⊗ᵢ iγ.symm)) ≪≫
      (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIsoFLT (baseChangeSnd c ψ) _ _).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIsoFLT (baseChangeSnd c ψ) _ _).symm⟩

theorem nonempty_fibreModule_iso :
    Nonempty (fibreModule c t (s' ≫ ψ1)
        (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ≅
      (Scheme.Modules.pullback (fibreIso R c t ψ1 s').hom).obj (fibreModule c (ψ1 ≫ t) s'
        ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
          (sectionTwist c ε (ψ1 ≫ t) r ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))) := by
  obtain ⟨iM⟩ := nonempty_Mγ_iso_pullback R c ε r Dγ t ψ1 L
  exact ⟨((Scheme.Modules.pullbackCongr (fibreIso_hom_fst_baseChangeSnd R c t ψ1 s')).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso R c t ψ1 s').hom
      (pullback.fst (pullback.snd c (ψ1 ≫ t)) s' ≫ baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t))).app _).symm ≪≫
    (Scheme.Modules.pullback (fibreIso R c t ψ1 s').hom).mapIso
      (((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c (ψ1 ≫ t)) s')
        (baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t))).app _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso iM.symm)⟩

theorem fibre_transport_to_t (𝒲 : (pullback (pullback.snd c (ψ1 ≫ t)) s').TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c t) (s' ≫ ψ1)).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c t (s' ≫ ψ1)) (fibreModule c t (s' ≫ ψ1)
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
          ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
            (sectionTwist c ε (ψ1 ≫ t) r ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))).H0) ∧
      Nonempty ((𝒱.sectionsOf (fibreAt c t (s' ≫ ψ1)) (fibreModule c t (s' ≫ ψ1)
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
          ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
            (sectionTwist c ε (ψ1 ≫ t) r ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε r Dγ t ψ1 L s'
  obtain ⟨𝒱, -, -, h0, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (s' ≫ ψ1)) (fibreAt c (ψ1 ≫ t) s') (fibreIso R c t ψ1 s') (fibreIso_hom_fibreAt R c t ψ1 s') 𝒲 _ _ eφ
  exact ⟨𝒱, h0, h1⟩

theorem fibre_transport_to_t' (𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ1)).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c (ψ1 ≫ t)) s').TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
          ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
            (sectionTwist c ε (ψ1 ≫ t) r ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))).H0 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ1)) (fibreModule c t (s' ≫ ψ1)
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0) ∧
      Nonempty ((𝒱.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
          ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
            (sectionTwist c ε (ψ1 ≫ t) r ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ1)) (fibreModule c t (s' ≫ ψ1)
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε r Dγ t ψ1 L s'

  let φ := fibreIso R c t ψ1 s'
  have hφ' : φ.symm.hom ≫ fibreAt c t (s' ≫ ψ1) = fibreAt c (ψ1 ≫ t) s' := by
    rw [Iso.symm_hom, Iso.inv_comp_eq, fibreIso_hom_fibreAt]

  have e' := ((Scheme.Modules.pullbackId _).app _).symm ≪≫
    ((Scheme.Modules.pullbackCongr φ.inv_hom_id).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app _).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso eφ.symm
  obtain ⟨𝒱, -, -, h0, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c (ψ1 ≫ t) s') (fibreAt c t (s' ≫ ψ1)) φ.symm hφ' 𝒲 _ _ e'
  exact ⟨𝒱, h0, h1⟩

end Transport

end AlgebraicGeometry.RelPicard.K5bSupply

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec Scheme IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Modules Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelPicard.baseChangeSnd Scheme.Modules.fltDual Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv RelEffCartierDiv.ext RelEffCartierDiv.pullbackAlong_comp SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover RelEffCartierDiv.twistModule_def Scheme.Modules.rigidify Scheme.Modules.rigidify_def Scheme.Modules.rigidifyMapIso Scheme.Modules.tensorTensorTensorComm Scheme.Modules.pullbackTensorObjIsoFLT Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsCartierFLT.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsCartierFLT Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.Modules.IsInvertible.nonempty_rigidify_pullback_tensor_iso RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback Scheme.IdealSheafData.comap_mulFLT)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd rigSection RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionIdeal sectionTwist fibreModule rigSection_snd RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre finrank_H0_fibre_eq_one_of_subsingleton_H1 nonempty_pullback_sectionTwist_iso)
namespace K5bUniv
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso.AlgebraicGeometry.RelPicard
open NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve
open P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso.AlgebraicGeometry.RelPicard.K5bSupply

variable {R : Type u} [CommRing R]

theorem pullbackAlong_I_eq_mul {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n m l : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') (D₀ : RelEffCartierDiv f m g') (E : RelEffCartierDiv f l g')
    (hD : D.I = D₀.I * E.I) {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (D.pullbackAlong φ hφ).I = (D₀.pullbackAlong φ hφ).I * (E.pullbackAlong φ hφ).I := by
  change D.I.comap _ = D₀.I.comap _ * E.I.comap _
  rw [hD, Scheme.IdealSheafData.comap_mulFLT]

variable (R) [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem UNIV'
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (U : T.Opens)
    (hUmax : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      (∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) → Set.range ⇑s ⊆ (U : Set T))
    (D : RelEffCartierDiv c r (U.ι ≫ t)) (D₀ : RelEffCartierDiv c g (U.ι ≫ t))
    (hD : D.I = D₀.I * (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).I)
    (hDL : Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L))
    {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t'] (ψ : SchemeHomOver t' t)
    (D' : RelEffCartierDiv c r t') (D₀' : RelEffCartierDiv c g t')
    (hD' : D'.I = D₀'.I * (Dγ.pullbackAlong t' (Category.comp_id _)).I)
    (hD'L : Nonempty (D'.twistModule c ε ≅ (L.pullbackAlong ψ).L))
    (h1' : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
      (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s'
          ((L.pullbackAlong ψ).L ⊗ (sectionTwist c ε t' r ⊗ (Dγ.pullbackAlong t' (Category.comp_id t')).idealModule)))).H1) :
    Set.range ⇑ψ.1 ⊆ (U : Set T) ∧
      ∀ (φ : T' ⟶ U) (hφ : φ ≫ U.ι = ψ.1),
        D' = D.pullbackAlong φ (by rw [← Category.assoc, hφ]; exact ψ.2) := by
  obtain ⟨ψ1, rfl⟩ := ψ
  subst hr

  set Lψ := L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t) with hLψ
  set DγT' := Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _) with hDγT'

  have hL' : FibrewiseAlgEquivZero Lψ := hL.pullback _
  have hfib' : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
      (𝒲 : (pullback (pullback.snd c (ψ1 ≫ t)) s').TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
        (Lψ.L ⊗ (sectionTwist c ε (ψ1 ≫ t) (g + e) ⊗ DγT'.idealModule)))).H1 ∧
      Module.finrank k (𝒲.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
        (Lψ.L ⊗ (sectionTwist c ε (ψ1 ≫ t) (g + e) ⊗ DγT'.idealModule)))).H0 = 1 :=
    fun k _ s' 𝒲 => ⟨h1' k s' 𝒲,
      finrank_H0_fibre_eq_one_of_subsingleton_H1 R c ε (g + e) e Dγ hχ (ψ1 ≫ t) Lψ hL' k s' 𝒲 (h1' k s' 𝒲)⟩
  refine ⟨?_, ?_⟩
  ·
    rintro _ ⟨y, rfl⟩
    have key := hUmax (T'.residueField y) (T'.fromSpecResidueField y ≫ ψ1) (fun 𝒲 => by
      obtain ⟨𝒱, -, ⟨e1⟩⟩ := fibre_transport_to_t' R c ε (g + e) Dγ t ψ1 L (T'.fromSpecResidueField y) 𝒲
      haveI := h1' _ (T'.fromSpecResidueField y) 𝒱
      exact e1.symm.toEquiv.subsingleton)
    refine key ⟨IsLocalRing.closedPoint (T'.residueField y), ?_⟩
    erw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  ·
    intro φ hφ
    have hφt : φ ≫ (U.ι ≫ t) = ψ1 ≫ t := by rw [← Category.assoc, hφ]

    have hM' : Scheme.Modules.IsInvertible (Lψ.L ⊗ (sectionTwist c ε (ψ1 ≫ t) (g + e) ⊗ DγT'.idealModule)) :=
      isInvertible_Mγ R c ε (ψ1 ≫ t) Lψ DγT'

    obtain ⟨N₁, hN₁, ⟨e₁⟩⟩ := exists_lineBundle_iso_of_twistModule_iso R c ε (ψ1 ≫ t) Lψ DγT' D₀' D' hD' hD'L

    have hD₂ : (D.pullbackAlong φ hφt).I = (D₀.pullbackAlong φ hφt).I * DγT'.I := by
      rw [pullbackAlong_I_eq_mul D D₀ _ hD φ hφt, hDγT', RelEffCartierDiv.pullbackAlong_comp]
      congr 2
      refine RelEffCartierDiv.ext ?_
      change Dγ.I.comap _ = Dγ.I.comap _
      congr 1
      simp only [hφ, ← Category.assoc]
    have hβcomp : baseChangeSnd c (⟨φ, hφt⟩ : SchemeHomOver (ψ1 ≫ t) (U.ι ≫ t)) ≫
        baseChangeSnd c (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t) =
          baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t) := by
      apply pullback.hom_ext
      · simp only [RelPicard.baseChangeSnd, Category.assoc, pullback.lift_fst, Category.comp_id]
      · simp only [RelPicard.baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hφ]
    have eL : (Scheme.Modules.pullback (baseChangeSnd c (⟨φ, hφt⟩ : SchemeHomOver (ψ1 ≫ t) (U.ι ≫ t)))).obj
        (L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L ≅ Lψ.L :=
      (Scheme.Modules.pullbackComp _ _).app L.L ≪≫ (Scheme.Modules.pullbackCongr hβcomp).app L.L
    have hDL₂ : Nonempty ((D.pullbackAlong φ hφt).twistModule c ε ≅ Lψ.L) := by
      obtain ⟨i⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε
        (⟨φ, hφt⟩ : SchemeHomOver (ψ1 ≫ t) (U.ι ≫ t)) D
      exact ⟨i ≪≫ (Scheme.Modules.pullback _).mapIso hDL.some ≪≫ eL⟩
    obtain ⟨N₂, hN₂, ⟨e₂⟩⟩ := exists_lineBundle_iso_of_twistModule_iso R c ε (ψ1 ≫ t) Lψ DγT'
      (D₀.pullbackAlong φ hφt) (D.pullbackAlong φ hφt) hD₂ hDL₂

    have huniq := relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre R c ε h𝔉 (ψ1 ≫ t)
      _ hM' hfib' D₀' (D₀.pullbackAlong φ hφt) N₁ N₂ hN₁ hN₂ e₁ e₂

    refine RelEffCartierDiv.ext ?_
    rw [hD', hD₂, huniq]

end AlgebraicGeometry.RelPicard.K5bUniv
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso.AlgebraicGeometry.RelPicard
open NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (U : T.Opens)
    (hUmax : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      (∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) → Set.range ⇑s ⊆ (U : Set T))
    (D : RelEffCartierDiv c r (U.ι ≫ t)) (D₀ : RelEffCartierDiv c g (U.ι ≫ t))
    (hD : D.I = D₀.I * (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).I)
    (hDL : Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L))
    {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t'] (ψ : SchemeHomOver t' t)
    (D' : RelEffCartierDiv c r t') (D₀' : RelEffCartierDiv c g t')
    (hD' : D'.I = D₀'.I * (Dγ.pullbackAlong t' (Category.comp_id _)).I)
    (hD'L : Nonempty (D'.twistModule c ε ≅ (L.pullbackAlong ψ).L))
    (h1' : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
      (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s'
          ((L.pullbackAlong ψ).L ⊗ (sectionTwist c ε t' r ⊗ (Dγ.pullbackAlong t' (Category.comp_id t')).idealModule)))).H1) :
    Set.range ⇑ψ.1 ⊆ (U : Set T) ∧
      ∀ (φ : T' ⟶ U) (hφ : φ ≫ U.ι = ψ.1),
        D' = D.pullbackAlong φ (by rw [← Category.assoc, hφ]; exact ψ.2) :=
  AlgebraicGeometry.RelPicard.K5bUniv.UNIV' R c ε h𝔉 g e r hr Dγ hχ t L hL U hUmax D D₀ hD hDL t' ψ D' D₀' hD' hD'L h1'
