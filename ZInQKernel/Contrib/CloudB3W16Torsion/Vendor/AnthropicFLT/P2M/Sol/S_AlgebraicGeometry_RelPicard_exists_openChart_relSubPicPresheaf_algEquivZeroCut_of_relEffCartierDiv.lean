/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesRigidify
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isAlgEquivZero_twistModule_fibre
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_isProper
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_isUniversal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_twistModule_and_nonempty_pullback_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_isAffineOpen_le_preimage_of_finset
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_forall_subsingleton_H1_fibre
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv.AlgebraicGeometry.RelPicard
open NeronModelInfra

noncomputable section

namespace AlgebraicGeometry
export AlgebraicGeometry (IsOpenImmersion.lift SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec Scheme IsOpenImmersion IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Opens.ι_apply Scheme.Modules Scheme.Opens IsOpenImmersion.lift_fac Scheme.Hom.comp_apply geometrically Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover Scheme.IdealSheafData.module RelEffCartierDiv RelEffCartierDiv.ext pullsBackOver_pullbackAlong RelEffCartierDiv.pullbackAlong_comp RelEffCartierDiv.twistModule Scheme.Modules.pullbackTensorObjIso RelEffCartierDiv.isAlgEquivZero_twistModule_fibre RelEffCartierDiv.exists_I_eq_mul RelEffCartierDiv.exists_isUniversal RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsInvertible Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.comap_mul)
namespace RelPicard
export AlgebraicGeometry.RelPicard (baseChangeSnd rigSection postComp RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero algEquivZeroCut RigidifiedLineBundle.pullbackAlongPullbackAlongIso relSubPicPresheaf sectionIdeal sectionTwist fibreModule exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1 relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso nonempty_pullback_sectionTwist_iso exists_opens_range_subset_iff_forall_subsingleton_H1_fibre)
namespace ChartOne
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv.AlgebraicGeometry.RelPicard
open NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

theorem pullbackAlong_congr_hom {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') {φ₁ φ₂ : T ⟶ T'} (h : φ₁ = φ₂) (h₁ : φ₁ ≫ g' = g)
    (h₂ : φ₂ ≫ g' = g) : D.pullbackAlong φ₁ h₁ = D.pullbackAlong φ₂ h₂ := by
  subst h; rfl

theorem pullbackAlong_I_eq_mul {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n m l : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') (D₀ : RelEffCartierDiv f m g')
    (E : RelEffCartierDiv f l g') (hD : D.I = D₀.I * E.I) {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    (D.pullbackAlong φ hφ).I = (D₀.pullbackAlong φ hφ).I * (E.pullbackAlong φ hφ).I := by
  change D.I.comap _ = D₀.I.comap _ * E.I.comap _
  rw [hD, Scheme.IdealSheafData.comap_mul]

theorem OverTotal_snd_eq_of_eq {Cat : Type*} [Category Cat] {S : Cat} {G : (Over S)ᵒᵖ ⥤ Type*} {T : Cat}
    {a b : G.OverTotal T} (h : a = b) :
    b.2 = G.map (Over.homMk (𝟙 T) (by simp [h]) : Over.mk b.1 ⟶ Over.mk a.1).op a.2 := by
  subst h
  exact (Functor.map_op_apply_eq_self _ (by simp) _).symm

theorem RigidifiedLineBundle_pullbackAlong_L_eq {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) {ψ ψ' : SchemeHomOver t' t} (h : ψ.1 = ψ'.1) :
    (M.pullbackAlong ψ).L = (M.pullbackAlong ψ').L := by
  rw [Subtype.ext h]

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
@[reassoc (attr := simp)]
theorem rigSection_snd' {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    rigSection c u ε ≫ pullback.snd c u = 𝟙 V :=
  pullback.lift_snd _ _ _

theorem isInvertible_sectionIdeal {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (sectionIdeal c ε u).IsInvertible :=
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c u) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c u inferInstance
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c u) (rigSection c u ε) (rigSection_snd' R c ε u)

theorem isInvertible_sectionTwist {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    Scheme.Modules.IsInvertible (sectionTwist c ε u n) :=
  ((isInvertible_sectionIdeal R c ε u).pow n).isInvertible_invModule

abbrev Mγ {e : ℕ} (n : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) {V : Scheme.{u}}
    (u : V ⟶ Spec (CommRingCat.of R)) (LV : RigidifiedLineBundle c ε u) : (pullback c u).Modules :=
  LV.L ⊗ (sectionTwist c ε u n ⊗ (Dγ.pullbackAlong u (Category.comp_id u)).idealModule)

theorem isInvertible_Mγ {e : ℕ} (n : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) (LV : RigidifiedLineBundle c ε u) :
    Scheme.Modules.IsInvertible (Mγ R c ε n Dγ u LV) :=
  LV.isInvertible.tensor ((isInvertible_sectionTwist R c ε u n).tensor
    (Dγ.pullbackAlong u (Category.comp_id u)).isInvertible_I.isInvertible_module)

section Transport

variable {e : ℕ} (n : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
  {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
  (ψ : SchemeHomOver t' t) (L : RigidifiedLineBundle c ε t)
  {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')

noncomputable def fibreIso : pullback (pullback.snd c t) (s' ≫ ψ.1) ≅ pullback (pullback.snd c t') s' :=
  pullbackLeftPullbackSndIso c t (s' ≫ ψ.1) ≪≫
    pullback.congrHom rfl (by rw [Category.assoc, ψ.2]) ≪≫ (pullbackLeftPullbackSndIso c t' s').symm

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem fibreIso_hom_fibreAt :
    (fibreIso R c t t' ψ s').hom ≫ fibreAt c t' s' = fibreAt c t (s' ≫ ψ.1) := by
  simp only [fibreIso, fibreAt, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem fibreIso_hom_fst_baseChangeSnd :
    (fibreIso R c t t' ψ s').hom ≫ pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ =
      pullback.fst (pullback.snd c t) (s' ≫ ψ.1) := by
  have hβ : baseChangeSnd c ψ =
      pullback.lift (pullback.fst c t' ≫ 𝟙 C) (pullback.snd c t' ≫ ψ.1)
        (by simp [ψ.2, pullback.condition]) := rfl
  rw [hβ]
  apply pullback.hom_ext
  · simp only [fibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_fst, Category.comp_id,
      pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullbackLeftPullbackSndIso_hom_fst]
  · simp only [fibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      pullbackLeftPullbackSndIso_inv_fst_snd_assoc, pullback.congrHom_hom,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

theorem nonempty_Mγ_iso_pullback :
    Nonempty (Mγ R c ε n Dγ t' (L.pullbackAlong ψ) ≅
      (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (Mγ R c ε n Dγ t L)) := by
  have hcomp : (Dγ.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ.1 ψ.2 =
      Dγ.pullbackAlong t' (Category.comp_id _) :=
    (RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _).trans
      (pullbackAlong_congr_hom Dγ ψ.2 _ _)
  have hI : (Dγ.pullbackAlong t' (Category.comp_id _)).I =
      (Dγ.pullbackAlong t (Category.comp_id t)).I.comap (baseChangeSnd c ψ) := by
    rw [← hcomp]; rfl
  have iγ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (Dγ.pullbackAlong t (Category.comp_id t)).idealModule ≅
      (Dγ.pullbackAlong t' (Category.comp_id _)).idealModule := by
    haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison (baseChangeSnd c ψ)
      (Dγ.pullbackAlong t (Category.comp_id t)).isInvertible_I
      (hI ▸ (Dγ.pullbackAlong t' (Category.comp_id _)).isInvertible_I)
    exact asIso ((Dγ.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison (baseChangeSnd c ψ)) ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hI).symm
  exact ⟨(Iso.refl _ ⊗ᵢ ((nonempty_pullback_sectionTwist_iso R c ε ψ n).some.symm ⊗ᵢ iγ.symm)) ≪≫
      (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm⟩

theorem nonempty_fibreModule_iso :
    Nonempty (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L) ≅
      (Scheme.Modules.pullback (fibreIso R c t t' ψ s').hom).obj
        (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))) := by
  obtain ⟨iM⟩ := nonempty_Mγ_iso_pullback R c ε n Dγ t t' ψ L
  exact ⟨((Scheme.Modules.pullbackCongr (fibreIso_hom_fst_baseChangeSnd R c t t' ψ s')).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso R c t t' ψ s').hom
      (pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ)).app _).symm ≪≫
    (Scheme.Modules.pullback (fibreIso R c t t' ψ s').hom).mapIso
      (((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c t') s') (baseChangeSnd c ψ)).app _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso iM.symm)⟩

theorem fibre_transport_to_t (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε n Dγ t t' ψ L s'
  obtain ⟨𝒱, -, -, -, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (s' ≫ ψ.1)) (fibreAt c t' s') (fibreIso R c t t' ψ s') (fibreIso_hom_fibreAt R c t t' ψ s') 𝒲 _ _ eφ
  exact ⟨𝒱, h1⟩

theorem fibre_transport_to_t' (𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c t') s').TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c t' s') (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε n Dγ t t' ψ L s'
  let φ := fibreIso R c t t' ψ s'
  have hφ' : φ.symm.hom ≫ fibreAt c t (s' ≫ ψ.1) = fibreAt c t' s' := by
    rw [Iso.symm_hom, Iso.inv_comp_eq, fibreIso_hom_fibreAt]
  have e' := ((Scheme.Modules.pullbackId _).app _).symm ≪≫
    ((Scheme.Modules.pullbackCongr φ.inv_hom_id).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app _).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso eφ.symm
  obtain ⟨𝒱, -, -, -, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t' s') (fibreAt c t (s' ≫ ψ.1)) φ.symm hφ' 𝒲 _ _ e'
  exact ⟨𝒱, h1⟩

theorem forall_subsingleton_H1_pullbackAlong
    (h : ∀ 𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L))).H1)
    (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))).H1 := by
  obtain ⟨𝒱, ⟨e1⟩⟩ := fibre_transport_to_t R c ε n Dγ t t' ψ L s' 𝒲
  haveI := h 𝒱
  exact e1.symm.toEquiv.subsingleton

theorem forall_subsingleton_H1_of_pullbackAlong
    (h : ∀ 𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))).H1)
    (𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L))).H1 := by
  obtain ⟨𝒱, ⟨e1⟩⟩ := fibre_transport_to_t' R c ε n Dγ t t' ψ L s' 𝒲
  haveI := h 𝒱
  exact e1.symm.toEquiv.subsingleton

end Transport

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in

theorem forall_subsingleton_H1_of_iso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {F F' : (pullback c t).Modules} (i : F ≅ F') {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (h : ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F')).H1 := by
  have e : fibreModule c t s F ≅ (Scheme.Modules.pullback (Iso.refl (pullback (pullback.snd c t) s)).hom).obj
      (fibreModule c t s F') :=
    (Scheme.Modules.pullback _).mapIso i ≪≫ ((Scheme.Modules.pullbackId _).app _).symm
  obtain ⟨𝒱, -, -, -, ⟨h1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) (fibreAt c t s) (Iso.refl _) (Category.id_comp _) 𝒲 _ _ e
  haveI := h 𝒱
  exact h1.symm.toEquiv.subsingleton

section Chart

set_option linter.unusedSectionVars false

variable [IsNoetherianRing R] [IsProper c] [GeometricallyIntegral c]
  (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
  (g e : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
  (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) (g + e) ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) (g + e) ⊗ Dγ.idealModule))).H1 = 1)
  {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) (𝒟 : RelEffCartierDiv c g y) (hU : 𝒟.IsUniversal)
  (DY : RelEffCartierDiv c (g + e) y) (hDY : DY.I = 𝒟.I * (Dγ.pullbackAlong y (Category.comp_id y)).I)

noncomputable def LY : RigidifiedLineBundle c ε y :=
  ⟨DY.twistModule c ε, (DY.isInvertible_twistModule_and_nonempty_pullback_iso c ε).1,
    (DY.isInvertible_twistModule_and_nonempty_pullback_iso c ε).2⟩

omit [IsNoetherianRing R] [IsProper c] [GeometricallyIntegral c] in
@[scoped simp] theorem LY_L : (LY R c ε g e y DY).L = DY.twistModule c ε := rfl

theorem fibrewiseAlgEquivZero_LY : FibrewiseAlgEquivZero (LY R c ε g e y DY) :=
  fun k _ _ s => DY.isAlgEquivZero_twistModule_fibre c ε k s

variable (UY : Y.Opens)
  (hUY : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Y),
    Set.range ⇑s ⊆ (UY : Set Y) ↔
      ∀ (𝒲 : (pullback (pullback.snd c y) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c y s) (fibreModule c y s (Mγ R c ε (g + e) Dγ y (LY R c ε g e y DY)))).H1)

noncomputable def chartElem :
    (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal.obj (op (UY : Scheme.{u})) :=
  ⟨UY.ι ≫ y, ⟨Quotient.mk _ ((LY R c ε g e y DY).pullbackAlong (⟨UY.ι, rfl⟩ : SchemeHomOver (UY.ι ≫ y) y)),
    (algEquivZeroCut c ε).pullback_mem _ _ _ _ (fibrewiseAlgEquivZero_LY R c ε g e y DY)⟩⟩

@[scoped simp] theorem chartElem_fst : (chartElem R c ε g e y DY UY).1 = UY.ι ≫ y := rfl

noncomputable def chartMap :
    uliftYoneda.{u + 1}.obj (UY : Scheme.{u}) ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal :=
  uliftYonedaEquiv.{u + 1, u, u + 1}.symm (chartElem R c ε g e y DY UY)

@[scoped simp] theorem uliftYonedaEquiv_chartMap :
    uliftYonedaEquiv.{u + 1, u, u + 1} (chartMap R c ε g e y DY UY) = chartElem R c ε g e y DY UY :=
  Equiv.apply_symm_apply _ _

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] [IsNoetherianRing R] [IsProper c] [GeometricallyIntegral c] in

theorem uliftYonedaEquiv_uliftYoneda_map_comp {F : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)} {T T' : Scheme.{u}} (ψ : T' ⟶ T)
    (f : uliftYoneda.{u + 1}.obj T ⟶ F) :
    uliftYonedaEquiv.{u + 1, u, u + 1} (uliftYoneda.{u + 1}.map ψ ≫ f) =
      F.map ψ.op (uliftYonedaEquiv.{u + 1, u, u + 1} f) :=
  (uliftYonedaEquiv_naturality f ψ.op).symm

theorem uliftYonedaEquiv_map_comp_chartMap {T : Scheme.{u}} (φ' : T ⟶ (UY : Scheme.{u})) :
    uliftYonedaEquiv.{u + 1, u, u + 1} (uliftYoneda.{u + 1}.map φ' ≫ chartMap R c ε g e y DY UY) =
      (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal.map φ'.op (chartElem R c ε g e y DY UY) := by
  rw [uliftYonedaEquiv_uliftYoneda_map_comp, uliftYonedaEquiv_chartMap]

def pointElem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t)
    (hL : FibrewiseAlgEquivZero L) :
    (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal.obj (op T) :=
  ⟨t, ⟨Quotient.mk _ L, hL⟩⟩

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] [IsNoetherianRing R] [IsProper c] [GeometricallyIntegral c] in
@[scoped simp] theorem pointElem_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t)
    (hL : FibrewiseAlgEquivZero L) : (pointElem R c ε t L hL).1 = t := rfl

include h𝔉 hχ hU hDY hUY

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t] (L : RigidifiedLineBundle c ε t)
  (hL : FibrewiseAlgEquivZero L) (U : T.Opens)
  (hUiff : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
    Set.range ⇑s ⊆ (U : Set T) ↔
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (Mγ R c ε (g + e) Dγ t L))).H1)
  (D : RelEffCartierDiv c (g + e) (U.ι ≫ t)) (D₀ : RelEffCartierDiv c g (U.ι ≫ t))
  (hD : D.I = D₀.I * (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).I)
  (hDL : Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L))

include hL hUiff hD hDL

theorem D_eq_pullbackAlong_lift : D = DY.pullbackAlong (hU.lift D₀) (hU.lift_comp D₀) := by
  refine RelEffCartierDiv.ext ?_
  rw [pullbackAlong_I_eq_mul DY 𝒟 _ hDY, hU.pullbackAlong_lift, RelEffCartierDiv.pullbackAlong_comp,
    pullbackAlong_congr_hom Dγ (hU.lift_comp D₀) _ (Category.comp_id _)]
  exact hD

theorem nonempty_LY_pullbackAlong_lift_iso :
    Nonempty (((LY R c ε g e y DY).pullbackAlong (⟨hU.lift D₀, hU.lift_comp D₀⟩ : SchemeHomOver (U.ι ≫ t) y)).L ≅
      (L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L) := by
  obtain ⟨i⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε
    (⟨hU.lift D₀, hU.lift_comp D₀⟩ : SchemeHomOver (U.ι ≫ t) y) DY
  exact ⟨i.symm ≪≫ eqToIso (congrArg (fun D' => RelEffCartierDiv.twistModule c ε D')
    (D_eq_pullbackAlong_lift R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hL U hUiff D D₀ hD hDL).symm) ≪≫ hDL.some⟩

theorem subsingleton_H1_U (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u}))
    (𝒲 : (pullback (pullback.snd c (U.ι ≫ t)) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c (U.ι ≫ t) s) (fibreModule c (U.ι ≫ t) s
      (Mγ R c ε (g + e) Dγ (U.ι ≫ t) (L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t))))).H1 := by
  have hrange : Set.range ⇑(s ≫ U.ι) ⊆ (U : Set T) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    exact (s x).2
  exact forall_subsingleton_H1_pullbackAlong R c ε (g + e) Dγ t (U.ι ≫ t) ⟨U.ι, rfl⟩ L s
    ((hUiff k (s ≫ U.ι)).1 hrange) 𝒲

theorem subsingleton_H1_U' (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u}))
    (𝒲 : (pullback (pullback.snd c (U.ι ≫ t)) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c (U.ι ≫ t) s) (fibreModule c (U.ι ≫ t) s
      (Mγ R c ε (g + e) Dγ (U.ι ≫ t)
        ((LY R c ε g e y DY).pullbackAlong (⟨hU.lift D₀, hU.lift_comp D₀⟩ : SchemeHomOver (U.ι ≫ t) y))))).H1 := by
  obtain ⟨i⟩ := nonempty_LY_pullbackAlong_lift_iso R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hL U hUiff D D₀ hD hDL
  exact forall_subsingleton_H1_of_iso R c (U.ι ≫ t) (i.symm ⊗ᵢ Iso.refl _) s
    (subsingleton_H1_U R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hL U hUiff D D₀ hD hDL k s) 𝒲

theorem range_lift_subset : Set.range ⇑(hU.lift D₀) ⊆ (UY : Set Y) := by
  rintro _ ⟨p, rfl⟩
  have key := (hUY ((U : Scheme.{u}).residueField p) ((U : Scheme.{u}).fromSpecResidueField p ≫ hU.lift D₀)).2
    (fun 𝒲 => forall_subsingleton_H1_of_pullbackAlong R c ε (g + e) Dγ y (U.ι ≫ t)
      ⟨hU.lift D₀, hU.lift_comp D₀⟩ (LY R c ε g e y DY) ((U : Scheme.{u}).fromSpecResidueField p)
      (subsingleton_H1_U' R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hL U hUiff D D₀ hD hDL _ ((U : Scheme.{u}).fromSpecResidueField p)) 𝒲)
  refine key ⟨IsLocalRing.closedPoint _, ?_⟩
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

noncomputable def φ : (U : Scheme.{u}) ⟶ (UY : Scheme.{u}) :=
  IsOpenImmersion.lift UY.ι (hU.lift D₀)
    (by rw [Scheme.Opens.range_ι]; exact range_lift_subset R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hL U hUiff D D₀ hD hDL)

@[reassoc (attr := simp)]
theorem φ_ι : φ R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hL U hUiff D D₀ hD hDL ≫ UY.ι = hU.lift D₀ :=
  IsOpenImmersion.lift_fac _ _ _

theorem clause_i (L' : RigidifiedLineBundle c ε t) (hL' : Nonempty (L'.L ≅ L.L))
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    Set.range ⇑s ⊆ (U : Set T) ↔
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (Mγ R c ε (g + e) Dγ t L'))).H1 := by
  refine (hUiff k s).trans ⟨fun h 𝒲 => ?_, fun h 𝒲 => ?_⟩
  · exact forall_subsingleton_H1_of_iso R c t (hL'.some.symm ⊗ᵢ Iso.refl _) s h 𝒲
  · exact forall_subsingleton_H1_of_iso R c t (hL'.some ⊗ᵢ Iso.refl _) s h 𝒲

theorem clause_ii :
    uliftYoneda.{u + 1}.map (φ R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hL U hUiff D D₀ hD hDL) ≫
        chartMap R c ε g e y DY UY =
      uliftYoneda.{u + 1}.map U.ι ≫ uliftYonedaEquiv.{u + 1, u, u + 1}.symm (pointElem R c ε t L hL) := by
  apply uliftYonedaEquiv.{u + 1, u, u + 1}.injective
  rw [uliftYonedaEquiv_map_comp_chartMap, uliftYonedaEquiv_uliftYoneda_map_comp, Equiv.apply_symm_apply]
  refine Functor.OverTotal.ext' ?_ ?_
  · change φ R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hL U hUiff D D₀ hD hDL ≫ UY.ι ≫ y = U.ι ≫ t
    rw [φ_ι_assoc, hU.lift_comp]
  · apply Subtype.ext
    refine Quotient.sound ⟨?_⟩
    refine RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      eqToIso (RigidifiedLineBundle_pullbackAlong_L_eq _ ?_) ≪≫
      (nonempty_LY_pullbackAlong_lift_iso R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hL U hUiff D D₀ hD hDL).some
    simp [postComp]

theorem clause_iii {T' : Scheme.{u}} (ψ : T' ⟶ T) (φ' : T' ⟶ (UY : Scheme.{u}))
    [LocallyOfFiniteType (ψ ≫ t)]
    (hφ' : uliftYoneda.{u + 1}.map φ' ≫ chartMap R c ε g e y DY UY =
      uliftYoneda.{u + 1}.map ψ ≫ uliftYonedaEquiv.{u + 1, u, u + 1}.symm (pointElem R c ε t L hL)) :
    ∃ χ : T' ⟶ (U : Scheme.{u}), χ ≫ U.ι = ψ ∧
      χ ≫ φ R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hL U hUiff D D₀ hD hDL = φ' := by

  have E := congrArg uliftYonedaEquiv.{u + 1, u, u + 1} hφ'
  rw [uliftYonedaEquiv_map_comp_chartMap, uliftYonedaEquiv_uliftYoneda_map_comp, Equiv.apply_symm_apply] at E
  have h1 : (φ' ≫ UY.ι) ≫ y = ψ ≫ t := by
    have := congrArg Sigma.fst E
    simpa [Functor.overTotal_map_fst] using this
  let Ψ : SchemeHomOver (ψ ≫ t) t := ⟨ψ, rfl⟩
  let Φ : SchemeHomOver (ψ ≫ t) y := ⟨φ' ≫ UY.ι, h1⟩

  have eL : Nonempty ((L.pullbackAlong Ψ).L ≅ ((LY R c ε g e y DY).pullbackAlong Φ).L) := by
    have h2 := OverTotal_snd_eq_of_eq E
    obtain ⟨i⟩ := Quotient.exact (congrArg Subtype.val h2)
    exact ⟨i ≪≫ RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      eqToIso (RigidifiedLineBundle_pullbackAlong_L_eq _ (by simp [postComp, Φ]))⟩

  have hD' : (DY.pullbackAlong (φ' ≫ UY.ι) h1).I =
      (𝒟.pullbackAlong (φ' ≫ UY.ι) h1).I * (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).I := by
    rw [pullbackAlong_I_eq_mul DY 𝒟 _ hDY, RelEffCartierDiv.pullbackAlong_comp,
      pullbackAlong_congr_hom Dγ h1 _ (Category.comp_id _)]
  have hD'L : Nonempty ((DY.pullbackAlong (φ' ≫ UY.ι) h1).twistModule c ε ≅ (L.pullbackAlong Ψ).L) := by
    obtain ⟨i⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε Φ DY
    exact ⟨i ≪≫ eL.some.symm⟩

  have h1' : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
      (𝒲 : (pullback (pullback.snd c (ψ ≫ t)) s').TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c (ψ ≫ t) s') (fibreModule c (ψ ≫ t) s'
        (Mγ R c ε (g + e) Dγ (ψ ≫ t) (L.pullbackAlong Ψ)))).H1 := by
    intro k _ s' 𝒲
    have hrange : Set.range ⇑(s' ≫ φ' ≫ UY.ι) ⊆ (UY : Set Y) := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (φ' (s' z)).2
    have hY := (hUY k (s' ≫ φ' ≫ UY.ι)).1 hrange
    have hT' := forall_subsingleton_H1_pullbackAlong R c ε (g + e) Dγ y (ψ ≫ t) Φ (LY R c ε g e y DY) s' hY
    exact forall_subsingleton_H1_of_iso R c (ψ ≫ t) (eL.some.symm ⊗ᵢ Iso.refl _) s' hT' 𝒲

  obtain ⟨hrangeU, huniq⟩ := relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso R c ε h𝔉 g e (g + e) rfl Dγ hχ
    t L hL U (fun k _ s h => (hUiff k s).2 h) D D₀ hD hDL (ψ ≫ t) Ψ
    (DY.pullbackAlong (φ' ≫ UY.ι) h1) (𝒟.pullbackAlong (φ' ≫ UY.ι) h1) hD' hD'L h1'

  have hrangeU' : Set.range ⇑ψ ⊆ Set.range ⇑U.ι := by rw [Scheme.Opens.range_ι]; exact hrangeU
  refine ⟨IsOpenImmersion.lift U.ι ψ hrangeU', IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have hχt : IsOpenImmersion.lift U.ι ψ hrangeU' ≫ U.ι ≫ t = ψ ≫ t := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]

  have hDD := huniq (IsOpenImmersion.lift U.ι ψ hrangeU') (IsOpenImmersion.lift_fac _ _ _)
  have hI : (𝒟.pullbackAlong (φ' ≫ UY.ι) h1).I * (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).I =
      (D₀.pullbackAlong (IsOpenImmersion.lift U.ι ψ hrangeU') hχt).I *
        (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).I := by
    rw [← hD', hDD, pullbackAlong_I_eq_mul D D₀ _ hD _ hχt, RelEffCartierDiv.pullbackAlong_comp,
      pullbackAlong_congr_hom Dγ hχt _ (Category.comp_id _)]
  have hI' : (𝒟.pullbackAlong (φ' ≫ UY.ι) h1).I = (D₀.pullbackAlong (IsOpenImmersion.lift U.ι ψ hrangeU') hχt).I := by
    rw [mul_comm, mul_comm (D₀.pullbackAlong _ hχt).I] at hI
    exact (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).isInvertible_I.mul_left_cancel hI

  have e1 : φ' ≫ UY.ι = hU.lift (𝒟.pullbackAlong (φ' ≫ UY.ι) h1) :=
    hU.eq_lift h1 (pullsBackOver_pullbackAlong 𝒟 (φ' ≫ UY.ι) h1)
  have e2 : IsOpenImmersion.lift U.ι ψ hrangeU' ≫ hU.lift D₀ = hU.lift (𝒟.pullbackAlong (φ' ≫ UY.ι) h1) := by
    refine hU.eq_lift (by rw [Category.assoc, hU.lift_comp, hχt]) ?_
    change (𝒟.pullbackAlong (IsOpenImmersion.lift U.ι ψ hrangeU' ≫ hU.lift D₀) _).I = (𝒟.pullbackAlong (φ' ≫ UY.ι) h1).I
    rw [hI', ← RelEffCartierDiv.pullbackAlong_comp 𝒟 (hU.lift D₀) (hU.lift_comp D₀) _ hχt, hU.pullbackAlong_lift]
  rw [← cancel_mono UY.ι, Category.assoc, φ_ι, e2, ← e1]

end Chart

end AlgebraicGeometry.RelPicard.ChartOne



open AlgebraicGeometry.RelPicard.ChartOne in

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
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1) :
    ∃ (X : Scheme.{u}) (f : uliftYoneda.{u + 1}.obj X ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv f).1 ∧
      ∀ ⦃T : Scheme.{u}⦄ (x : uliftYoneda.{u + 1}.obj T ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
        LocallyOfFiniteType (uliftYonedaEquiv x).1 →
        ∃ (U : T.Opens) (φ : (↑U : Scheme.{u}) ⟶ X),
          (∀ (L : RigidifiedLineBundle c ε (uliftYonedaEquiv x).1), Quotient.mk _ L = (uliftYonedaEquiv x).2.1 →
            ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
              Set.range ⇑s ⊆ (U : Set T) ↔
                ∀ (𝒲 : (pullback (pullback.snd c (uliftYonedaEquiv x).1) s).TwoAffineOpenCover),
                  Subsingleton (𝒲.sectionsOf (fibreAt c (uliftYonedaEquiv x).1 s) (fibreModule c (uliftYonedaEquiv x).1 s
                    (L.L ⊗ (sectionTwist c ε (uliftYonedaEquiv x).1 r ⊗
                      (Dγ.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)))).H1) ∧
          uliftYoneda.{u + 1}.map φ ≫ f = uliftYoneda.{u + 1}.map U.ι ≫ x ∧
          ∀ ⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ T) (φ' : T' ⟶ X),
            LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x).1) →
            uliftYoneda.{u + 1}.map φ' ≫ f = uliftYoneda.{u + 1}.map ψ ≫ x →
            ∃ χ : T' ⟶ ↑U, χ ≫ U.ι = ψ ∧ χ ≫ φ = φ' := by
  subst hr

  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨Y, y, 𝒟, hU⟩ := RelEffCartierDiv.exists_isUniversal c 𝔉.exists_isAffineOpen_le_preimage_of_finset g
  haveI : IsProper y := hU.isProper

  obtain ⟨DY, hDY⟩ := RelEffCartierDiv.exists_I_eq_mul 𝒟 (Dγ.pullbackAlong y (Category.comp_id y))

  obtain ⟨UY, hUY⟩ := exists_opens_range_subset_iff_forall_subsingleton_H1_fibre R c ε h𝔉 y
    (Mγ R c ε (g + e) Dγ y (LY R c ε g e y DY)) (isInvertible_Mγ R c ε (g + e) Dγ y _)
  refine ⟨UY, chartMap R c ε g e y DY UY, ?_, ?_⟩
  ·
    rw [uliftYonedaEquiv_chartMap]
    change LocallyOfFiniteType (UY.ι ≫ y)
    infer_instance
  intro T x hx

  generalize hxa : uliftYonedaEquiv x = a at hx ⊢
  obtain rfl : x = uliftYonedaEquiv.symm a := by rw [← hxa, Equiv.symm_apply_apply]
  clear hxa
  change (relSubPicPresheaf c ε (algEquivZeroCut c ε)).OverTotal T at a
  obtain ⟨t, ⟨ξ, hξ⟩⟩ := a
  obtain ⟨L, rfl⟩ := Quotient.exists_rep ξ
  change FibrewiseAlgEquivZero L at hξ
  haveI : LocallyOfFiniteType t := hx
  change ∃ (U : T.Opens) (φ : (↑U : Scheme.{u}) ⟶ UY), _ ∧
    uliftYoneda.{u + 1}.map φ ≫ _ = uliftYoneda.{u + 1}.map U.ι ≫ uliftYonedaEquiv.symm (pointElem R c ε t L hξ) ∧ _

  obtain ⟨U, hUiff⟩ := exists_opens_range_subset_iff_forall_subsingleton_H1_fibre R c ε h𝔉 t
    (Mγ R c ε (g + e) Dγ t L) (isInvertible_Mγ R c ε (g + e) Dγ t L)
  obtain ⟨D, D₀, hD, hDL⟩ := exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1 R c ε h𝔉 g e (g + e) rfl
    Dγ hχ t L hξ U (fun k _ s hs => (hUiff k s).1 hs)
  refine ⟨U, φ R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hξ U hUiff D D₀ hD hDL, ?_, ?_, ?_⟩
  · intro L' hL' k _ s
    exact clause_i R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hξ U hUiff D D₀ hD hDL L' (Quotient.exact hL') k s
  · exact clause_ii R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hξ U hUiff D D₀ hD hDL
  · intro T' ψ φ' hlft hφ'
    haveI := hlft
    exact clause_iii R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hξ U hUiff D D₀ hD hDL ψ φ' hφ'
