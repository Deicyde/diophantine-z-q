/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H1_unit_fibre_eq_of_eulerChar_chart
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1

set_option autoImplicit false

universe u

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec Scheme smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr Scheme.Opens.ι_apply Scheme.Modules Scheme.Opens Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv RelEffCartierDiv.pullbackAlong_comp SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover RelEffCartierDiv.twistModule_def Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso Scheme.Modules.tensorTensorTensorComm Scheme.Modules.pullbackTensorObjIsoFLT Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsCartierFLT.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsCartierFLT Scheme.Hom.isInvertible_ker_of_comp_eq_id RelEffCartierDiv.exists_I_eq_mul Scheme.Modules.IsInvertible.nonempty_rigidify_pullback_tensor_iso)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd rigSection RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionIdeal sectionTwist fibreModule rigSection_snd RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre finrank_H1_unit_fibre_eq_of_eulerChar_chart finrank_H0_fibre_eq_one_of_subsingleton_H1 nonempty_pullback_sectionTwist_iso)
namespace K5bExist
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1.AlgebraicGeometry.RelPicard
open NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
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

theorem hfib_of_hU
    (r e : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (U : T.Opens)
    (hU : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T), Set.range ⇑s ⊆ (U : Set T) →
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1)
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u}))
    (𝒲 : (pullback (pullback.snd c (U.ι ≫ t)) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c (U.ι ≫ t) s) (fibreModule c (U.ι ≫ t) s
        ((L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L ⊗
          (sectionTwist c ε (U.ι ≫ t) r ⊗ (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).idealModule)))).H1 ∧
      Module.finrank k (𝒲.sectionsOf (fibreAt c (U.ι ≫ t) s) (fibreModule c (U.ι ≫ t) s
        ((L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L ⊗
          (sectionTwist c ε (U.ι ≫ t) r ⊗ (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).idealModule)))).H0 = 1 := by

  let ψ : SchemeHomOver (U.ι ≫ t) t := ⟨U.ι, rfl⟩
  set Mt : (pullback c t).Modules :=
    L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule) with hMt
  set Mu : (pullback c (U.ι ≫ t)).Modules := (L.pullbackAlong ψ).L ⊗
    (sectionTwist c ε (U.ι ≫ t) r ⊗ (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).idealModule) with hMu
  have hβ : baseChangeSnd c ψ = pullback.lift (pullback.fst c (U.ι ≫ t) ≫ 𝟙 C) (pullback.snd c (U.ι ≫ t) ≫ U.ι)
      (by simp [pullback.condition]) := rfl

  have hcomp : (Dγ.pullbackAlong t (Category.comp_id t)).pullbackAlong U.ι ψ.2 =
      Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _) :=
    RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _
  have hI : (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).I =
      (Dγ.pullbackAlong t (Category.comp_id t)).I.comap (baseChangeSnd c ψ) := by
    rw [← hcomp]; rfl
  have iγ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (Dγ.pullbackAlong t (Category.comp_id t)).idealModule ≅
      (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).idealModule := by
    haveI := Scheme.IdealSheafData.IsCartierFLT.isIso_pullbackModuleComparison (baseChangeSnd c ψ)
      (Dγ.pullbackAlong t (Category.comp_id t)).isInvertible_I
      (hI ▸ (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).isInvertible_I)
    exact asIso ((Dγ.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison (baseChangeSnd c ψ)) ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hI).symm

  have iM : Mu ≅ (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj Mt :=
    (Iso.refl _ ⊗ᵢ ((nonempty_pullback_sectionTwist_iso R c ε ψ r).some.symm ⊗ᵢ iγ.symm)) ≪≫
      (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIsoFLT (baseChangeSnd c ψ) _ _).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIsoFLT (baseChangeSnd c ψ) _ _).symm

  let φ : pullback (pullback.snd c t) (s ≫ U.ι) ≅ pullback (pullback.snd c (U.ι ≫ t)) s :=
    pullbackLeftPullbackSndIso c t (s ≫ U.ι) ≪≫ pullback.congrHom rfl (Category.assoc s U.ι t) ≪≫
      (pullbackLeftPullbackSndIso c (U.ι ≫ t) s).symm
  have hφsnd : φ.hom ≫ fibreAt c (U.ι ≫ t) s = fibreAt c t (s ≫ U.ι) := by
    simp only [φ, fibreAt, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  have hφfst : φ.hom ≫ pullback.fst (pullback.snd c (U.ι ≫ t)) s ≫ baseChangeSnd c ψ =
      pullback.fst (pullback.snd c t) (s ≫ U.ι) := by
    rw [hβ]
    apply pullback.hom_ext
    · simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_fst, Category.comp_id,
        pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullbackLeftPullbackSndIso_hom_fst]
    · simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        pullbackLeftPullbackSndIso_inv_fst_snd_assoc, pullback.congrHom_hom,
        Category.comp_id, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

  have eφ : fibreModule c t (s ≫ U.ι) Mt ≅ (Scheme.Modules.pullback φ.hom).obj (fibreModule c (U.ι ≫ t) s Mu) :=
    ((Scheme.Modules.pullbackCongr hφfst).app Mt).symm ≪≫
    ((Scheme.Modules.pullbackComp φ.hom
      (pullback.fst (pullback.snd c (U.ι ≫ t)) s ≫ baseChangeSnd c ψ)).app Mt).symm ≪≫
    (Scheme.Modules.pullback φ.hom).mapIso
      (((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c (U.ι ≫ t)) s) (baseChangeSnd c ψ)).app Mt).symm ≪≫
        (Scheme.Modules.pullback _).mapIso iM.symm)

  obtain ⟨𝒱, -, -, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (s ≫ U.ι)) (fibreAt c (U.ι ≫ t) s) φ hφsnd 𝒲 (fibreModule c (U.ι ≫ t) s Mu) (fibreModule c t (s ≫ U.ι) Mt) eφ
  have hrange : Set.range ⇑(s ≫ U.ι) ⊆ (U : Set T) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    exact (s x).2
  have h1 : Subsingleton (𝒱.sectionsOf (fibreAt c t (s ≫ U.ι)) (fibreModule c t (s ≫ U.ι) Mt)).H1 := hU k (s ≫ U.ι) hrange 𝒱
  haveI := h1
  refine ⟨e1.symm.toEquiv.subsingleton, ?_⟩
  rw [← finrank_H0_fibre_eq_one_of_subsingleton_H1 R c ε r e Dγ hχ t L hL k (s ≫ U.ι) 𝒱 h1]
  exact e0.symm.finrank_eq

theorem EXIST'
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
    (hU : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T), Set.range ⇑s ⊆ (U : Set T) →
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) :
    ∃ (D : RelEffCartierDiv c r (U.ι ≫ t)) (D₀ : RelEffCartierDiv c g (U.ι ≫ t)),
      D.I = D₀.I * (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).I ∧
      Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L) := by
  subst hr

  have hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (𝟙_ (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).Modules)).H1 = g :=
    fun k _ _ x 𝒲 => finrank_H1_unit_fibre_eq_of_eulerChar_chart R c ε g e (g + e) rfl Dγ hχ k x 𝒲

  have hfib := hfib_of_hU R c ε (g + e) e Dγ hχ t L hL U hU

  have hM : Scheme.Modules.IsInvertible ((L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L ⊗
      (sectionTwist c ε (U.ι ≫ t) (g + e) ⊗ (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).idealModule)) :=
    (L.pullbackAlong _).isInvertible.tensor ((isInvertible_sectionTwist R c ε (U.ι ≫ t) (g + e)).tensor
      (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).isInvertible_I.isInvertible_module)
  obtain ⟨D₀, N, hN, ⟨e₀⟩, -⟩ :=
    exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre R c ε h𝔉 g hg (U.ι ≫ t) _ hM hfib
  obtain ⟨D, hD⟩ := RelEffCartierDiv.exists_I_eq_mul D₀ (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _))
  exact ⟨D, D₀, hD, nonempty_twistModule_iso R c ε (U.ι ≫ t) _ _ D₀ D hD N hN e₀⟩

end AlgebraicGeometry.RelPicard.K5bExist
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1.AlgebraicGeometry.RelPicard
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
    (hU : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T), Set.range ⇑s ⊆ (U : Set T) →
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) :
    ∃ (D : RelEffCartierDiv c r (U.ι ≫ t)) (D₀ : RelEffCartierDiv c g (U.ι ≫ t)),
      D.I = D₀.I * (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).I ∧
      Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L) :=
  AlgebraicGeometry.RelPicard.K5bExist.EXIST' R c ε h𝔉 g e r hr Dγ hχ t L hL U hU
