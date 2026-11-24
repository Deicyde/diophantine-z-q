/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_mono_whiskerLeft_moduleIota
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_projectionMorphism_of_iso_free
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_pullback_map_projectionMorphism_iff
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
-- [port] Source-local namespace is declared below; existing root namespace remains open.
open Opposite
open TopologicalSpace
open CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal

noncomputable section

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Modules.presheaf Scheme.Modules.Hom Scheme Scheme.Modules.Hom.app IsClosedImmersion Scheme.Modules.pullbackPushforwardAdjunction Scheme.isBasis_affineOpens isClosedImmersion_iff_isAffineHom Scheme.Modules Scheme.IdealSheafData Scheme.Modules.IsLocallyFreeOfRank Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.projectionMorphism Scheme.Modules.projectionMorphism_def Scheme.Modules.projectionMorphismMate_def Scheme.Modules.pullbackLocalSection Scheme.Modules.pullbackLocalSection_smul Scheme.Modules.homEquiv_symm_app_pullbackLocalSection Scheme.Modules.pullback_hom_extFLT Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.isIso_projectionMorphism_of_iso_free Scheme.Modules.isIso_pullback_map_projectionMorphism_iff Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection Scheme.Modules.unitSection Scheme.Modules.smul_unitSection Scheme.Modules.IsInvertible Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pushforward Modules.pullback Hom mk Modules.presheaf Γ Hom.app Modules.Hom Modules.Hom.app Modules.pullbackPushforwardAdjunction isBasis_affineOpens Modules Opens IdealSheafData evaluation Modules.IsLocallyFreeOfRank Modules.pullbackTensorUnitObjIso Modules.projectionMorphism Modules.projectionMorphism_def Modules.projectionMorphismMate_def Modules.pullbackLocalSection Modules.pullbackLocalSection_smul Modules.homEquiv_symm_app_pullbackLocalSection Modules.pullback_hom_extFLT Modules.Hom.epi_iff_locallySurjective Modules.isIso_projectionMorphism_of_iso_free Modules.isIso_pullback_map_projectionMorphism_iff Modules.Hom.isIso_of_forall_exists_isIso_pullback_map Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection Modules.unitSection Modules.smul_unitSection Modules.IsInvertible Modules.isLocallyFreeOfRank_one_iff_isInvertible" namespace IdealSheafData p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "mk map subscheme map_id ideal map_comp inclusion subschemeι module moduleι invModule mono_whiskerLeft_moduleIota IsCartierFLT" end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData in
private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.uMod {X : Scheme.{u}} (I : X.IdealSheafData) :
    ((𝟙_ X.Modules : X.Modules) ⟶
      ((Scheme.Modules.pushforward I.subschemeι).obj (𝟙_ I.subscheme.Modules) : X.Modules)) :=
  I.subschemeι.unitToPushforwardUnit

end AlgebraicGeometry.Scheme.IdealSheafData
-- [port] No export is needed for the private helper: uMod)
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.moduleι_comp_uMod {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.moduleι ≫ I.uMod = 0 :=
  kernel.condition I.subschemeι.unitToPushforwardUnit

end AlgebraicGeometry.Scheme.IdealSheafData
-- [port] No export is needed for the private helper: moduleι_comp_uMod)
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.mono_moduleι' {X : Scheme.{u}} (I : X.IdealSheafData) :
    Mono I.moduleι :=
  ⟨fun g g' w => (cancel_mono (kernel.ι I.subschemeι.unitToPushforwardUnit)).mp w⟩

end AlgebraicGeometry.Scheme.IdealSheafData
-- [port] No export is needed for the private helper: mono_moduleι')
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.epi_uMod
    {X : Scheme.{u}} (I : X.IdealSheafData) : Epi I.uMod := by
  refine (AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective _).mpr ?_
  intro U s x hxU
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) hxU
  refine ⟨V, hVU, hxV, ?_⟩
  have hsurj := (isClosedImmersion_iff_isAffineHom.mp (inferInstance : IsClosedImmersion I.subschemeι)).2 V hV
  obtain ⟨a, ha⟩ := hsurj ((Scheme.Modules.presheaf ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
    (SheafOfModules.unit I.subscheme.ringCatSheaf))).map (homOfLE hVU).op s)
  exact ⟨a, ha⟩

end AlgebraicGeometry.Scheme.IdealSheafData
-- [port] No export is needed for the private helper: epi_uMod)
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData in
private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.unitSeq {X : Scheme.{u}} (I : X.IdealSheafData) :
    ShortComplex X.Modules :=
  ShortComplex.mk I.moduleι I.uMod I.moduleι_comp_uMod

end AlgebraicGeometry.Scheme.IdealSheafData
-- [port] No export is needed for the private helper: unitSeq)
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.shortExact_unitSeq
    {X : Scheme.{u}} (I : X.IdealSheafData) : I.unitSeq.ShortExact := by
  haveI := I.epi_uMod
  haveI := I.mono_moduleι'
  refine ShortComplex.ShortExact.mk' ?_ (by change Mono I.moduleι; infer_instance) (by change Epi I.uMod; infer_instance)
  exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel I.subschemeι.unitToPushforwardUnit)

end AlgebraicGeometry.Scheme.IdealSheafData
-- [port] No export is needed for the private helper: shortExact_unitSeq)
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData in
private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.tensorSeq {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (F ◁ I.moduleι) (F ◁ I.uMod)
    (by
      change (tensorLeft F).map _ ≫ (tensorLeft F).map _ = 0
      rw [← Functor.map_comp, I.moduleι_comp_uMod]
      exact Functor.map_zero _ _ _)

end AlgebraicGeometry.Scheme.IdealSheafData
-- [port] No export is needed for the private helper: tensorSeq)
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.shortExact_tensorSeq {X : Scheme.{u}} (I : X.IdealSheafData)
    {n : ℕ} (F : X.Modules) (hF : Scheme.Modules.IsLocallyFreeOfRank n F) :
    (I.tensorSeq F).ShortExact := by
  haveI := I.mono_whiskerLeft_moduleIota F hF
  haveI := I.epi_uMod
  let G : X.Modules ⥤ X.Modules := tensorLeft F

  have hcok : IsColimit (CokernelCofork.ofπ (I.tensorSeq F).g (I.tensorSeq F).zero) := by
    have h0 := I.shortExact_unitSeq.gIsCokernel
    have h1 := CokernelCofork.mapIsColimit _ h0 G
    refine IsColimit.ofIsoColimit h1 (Cofork.ext (Iso.refl _) ?_)
    erw [Category.comp_id]
    rfl
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hcok) ?_ ?_
  · change Mono (F ◁ I.moduleι); infer_instance
  · change Epi ((tensorLeft F).map I.uMod); infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData
-- [port] No export is needed for the private helper: shortExact_tensorSeq)
namespace Ws31IdealSES

variable {Z X : Scheme.{u}}

theorem isIso_projectionMorphism (i : Z ⟶ X) {m : ℕ} (G : X.Modules)
    (hG : Scheme.Modules.IsLocallyFreeOfRank m G) :
    IsIso (Scheme.Modules.projectionMorphism i G) := by
  apply Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hG.exists_trivialization x
  refine ⟨U, hx, ?_⟩
  rw [Scheme.Modules.isIso_pullback_map_projectionMorphism_iff]
  exact Scheme.Modules.isIso_projectionMorphism_of_iso_free (i ∣_ U) _ e

abbrev toFun (U : X.Opens) (s : Γ(𝟙_ X.Modules, U)) : Γ(X, U) := s

lemma eq_smul_unitSection (U : X.Opens) (s : Γ(𝟙_ X.Modules, U)) :
    s = toFun U s • Scheme.Modules.unitSection U :=
  (Scheme.Modules.smul_unitSection (toFun U s)).symm

theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection (f : Z ⟶ X) (U : X.Opens)
    (s : Γ(𝟙_ X.Modules, U)) :
    (Scheme.Modules.pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f s) =
      f.app U (toFun U s) := by
  conv_lhs => rw [eq_smul_unitSection U s]
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection]
  exact Scheme.Modules.smul_unitSection _

theorem η_pullback_eq (f : Z ⟶ X) :
    η (Scheme.Modules.pullback f) = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  apply Scheme.Modules.pullback_hom_extFLT
  intro U s
  change (Scheme.Modules.pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f s) = _
  rw [pullbackTensorUnitObjIso_hom_app_pullbackLocalSection]
  change _ = Scheme.Modules.Hom.app (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    f.unitToPushforwardUnit) (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f s)
  rw [Scheme.Modules.homEquiv_symm_app_pullbackLocalSection]
  rfl

abbrev uX (i : Z ⟶ X) :
    ((𝟙_ X.Modules : X.Modules) ⟶ ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) : X.Modules)) :=
  i.unitToPushforwardUnit

theorem unit_app_eq (i : Z ⟶ X) (G : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G =
      (λ_ G).inv ≫ (uX i ▷ G) ≫ Scheme.Modules.projectionMorphism i G := by
  rw [Scheme.Modules.projectionMorphism_def, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_id]
  congr 1
  rw [Scheme.Modules.projectionMorphismMate_def]
  rw [Functor.Monoidal.μIso_inv, ← δ_natural_left_assoc, ← comp_whiskerRight_assoc]
  have hc : (Scheme.Modules.pullback i).map (uX i) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules) =
        η (Scheme.Modules.pullback i) := by
    rw [η_pullback_eq]
    rfl
  rw [hc, left_unitality_hom, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

theorem rightUnitor_hom_comp_leftUnitor_inv (G : X.Modules) :
    (ρ_ G).hom ≫ (λ_ G).inv = (β_ G (𝟙_ X.Modules)).hom := by
  rw [← braiding_leftUnitor, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem whiskerLeft_moduleι_comp_unit (I : X.IdealSheafData) (G : X.Modules) :
    ((G ◁ I.moduleι) ≫ (ρ_ G).hom) ≫ (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G = 0 := by
  rw [unit_app_eq, Category.assoc, ← Category.assoc (ρ_ G).hom, rightUnitor_hom_comp_leftUnitor_inv,
    ← Category.assoc (β_ _ _).hom, ← BraidedCategory.braiding_naturality_right, Category.assoc, ← Category.assoc (G ◁ I.moduleι),
    ← MonoidalCategory.whiskerLeft_comp]
  change (tensorLeft G).map (I.moduleι ≫ I.uMod) ≫ _ = 0
  rw [I.moduleι_comp_uMod, Functor.map_zero, zero_comp]

theorem exists_shortExact_unit (I : X.IdealSheafData) {m : ℕ} (G : X.Modules)
    (hG : Scheme.Modules.IsLocallyFreeOfRank m G) :
    ∃ w : ((G ◁ I.moduleι) ≫ (ρ_ G).hom) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G = 0,
      (ShortComplex.mk ((G ◁ I.moduleι) ≫ (ρ_ G).hom)
        ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G) w).ShortExact := by
  haveI := isIso_projectionMorphism I.subschemeι G hG
  refine ⟨whiskerLeft_moduleι_comp_unit I G, ?_⟩
  refine ShortComplex.shortExact_of_iso ?_ (I.shortExact_tensorSeq G hG)
  refine ShortComplex.isoMk (Iso.refl _) (ρ_ G)
    ((β_ G _) ≪≫ asIso (Scheme.Modules.projectionMorphism I.subschemeι G)) ?_ ?_
  · change 𝟙 _ ≫ ((G ◁ I.moduleι) ≫ (ρ_ G).hom) = (G ◁ I.moduleι) ≫ (ρ_ G).hom
    rw [Category.id_comp]
  · change (ρ_ G).hom ≫ (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G =
      (G ◁ I.uMod) ≫ (β_ G _).hom ≫ Scheme.Modules.projectionMorphism I.subschemeι G
    rw [unit_app_eq, ← Category.assoc (ρ_ G).hom, rightUnitor_hom_comp_leftUnitor_inv,
      ← Category.assoc (β_ _ _).hom, ← BraidedCategory.braiding_naturality_right, Category.assoc]
    rfl

theorem epi_unit_app (I : X.IdealSheafData) {m : ℕ} (G : X.Modules)
    (hG : Scheme.Modules.IsLocallyFreeOfRank m G) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G) := by
  obtain ⟨w, h⟩ := exists_shortExact_unit I G hG
  exact h.epi_g

end Ws31IdealSES

namespace Ws31EvKer

open Ws31IdealSES

variable {X : Scheme.{u}}

set_option maxHeartbeats 6400000 in

theorem nonempty_twistIso (𝓘 : X.IdealSheafData) (h𝓘 : 𝓘.IsCartierFLT) (L : X.Modules) (d n : ℕ) :
    Nonempty ((L ⊗ (𝓘 ^ (d + n)).invModule) ⊗ (𝓘 ^ n).module ≅ L ⊗ (𝓘 ^ d).invModule) := by
  obtain ⟨e431⟩ := (h𝓘.pow d).nonempty_mul_invModule_iso_tensor (h𝓘.pow n)
  obtain ⟨-, ⟨eMn⟩⟩ := (h𝓘.pow n).isInvertible_module.dual
  let ePow : (𝓘 ^ (d + n)).invModule ≅ (𝓘 ^ d * 𝓘 ^ n).invModule := eqToIso (by rw [pow_add])
  let eG : L ⊗ (𝓘 ^ (d + n)).invModule ≅ L ⊗ ((𝓘 ^ d).invModule ⊗ (𝓘 ^ n).invModule) :=
    whiskerLeftIso L (ePow ≪≫ e431)
  let eN : (𝓘 ^ n).invModule ⊗ (𝓘 ^ n).module ≅ 𝟙_ X.Modules := β_ _ _ ≪≫ eMn
  exact ⟨whiskerRightIso eG _ ≪≫ α_ L _ _ ≪≫
    whiskerLeftIso L (α_ _ _ _ ≪≫ whiskerLeftIso _ eN ≪≫ ρ_ _)⟩

theorem main (𝓘 : X.IdealSheafData) (h𝓘 : 𝓘.IsCartierFLT)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (r n d : ℕ) (hd : d + n = r) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ n).subschemeι)).unit.app (L ⊗ (𝓘 ^ r).invModule)) ∧
      ∃ (ι : L ⊗ (𝓘 ^ d).invModule ⟶ L ⊗ (𝓘 ^ r).invModule)
        (w : ι ≫ (Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ n).subschemeι)).unit.app
          (L ⊗ (𝓘 ^ r).invModule) = 0),
        (ShortComplex.mk ι _ w).ShortExact := by
  subst hd
  have hG : Scheme.Modules.IsInvertible (L ⊗ (𝓘 ^ (d + n)).invModule) :=
    hL.tensor (h𝓘.pow (d + n)).isInvertible_invModule
  have hG1 : Scheme.Modules.IsLocallyFreeOfRank 1 (L ⊗ (𝓘 ^ (d + n)).invModule) :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr hG
  obtain ⟨w, hS⟩ := exists_shortExact_unit (𝓘 ^ n) (L ⊗ (𝓘 ^ (d + n)).invModule) hG1
  obtain ⟨e⟩ := nonempty_twistIso 𝓘 h𝓘 L d n
  refine ⟨hS.epi_g, e.inv ≫ (((L ⊗ (𝓘 ^ (d + n)).invModule) ◁ (𝓘 ^ n).moduleι) ≫ (ρ_ _).hom), ?_, ?_⟩
  · rw [Category.assoc, w, comp_zero]
  · refine ShortComplex.shortExact_of_iso
      (S₁ := ShortComplex.mk ((((L ⊗ (𝓘 ^ (d + n)).invModule) ◁ (𝓘 ^ n).moduleι) ≫ (ρ_ _).hom))
        ((Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ n).subschemeι)).unit.app
          (L ⊗ (𝓘 ^ (d + n)).invModule)) w) ?_ hS
    refine ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) ?_ ?_
    · change e.hom ≫ e.inv ≫ _ = _ ≫ 𝟙 _
      rw [Iso.hom_inv_id_assoc, Category.comp_id]
    · change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]

end Ws31EvKer

end

theorem solution
    {X : Scheme.{u}} (𝓘 : X.IdealSheafData) (h𝓘 : 𝓘.IsCartierFLT)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (r n d : ℕ) (hd : d + n = r) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ n).subschemeι)).unit.app (L ⊗ (𝓘 ^ r).invModule)) ∧
      ∃ (ι : L ⊗ (𝓘 ^ d).invModule ⟶ L ⊗ (𝓘 ^ r).invModule)
        (w : ι ≫ (Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ n).subschemeι)).unit.app
          (L ⊗ (𝓘 ^ r).invModule) = 0),
        (ShortComplex.mk ι _ w).ShortExact :=
  Ws31EvKer.main 𝓘 h𝓘 L hL r n d hd
