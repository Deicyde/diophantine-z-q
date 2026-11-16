/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_and_isIso_curry_braiding_ev
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ofUnitSection_sectionDual_app
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
-- Original source-local namespace open deferred until after its declaration.

noncomputable section

namespace ZeroSchemeCanonMC
open CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

def toBidual (M : C) : M ⟶ (ihom ((ihom M).obj (𝟙_ C))).obj (𝟙_ C) :=
  MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C))

omit [BraidedCategory C] in

theorem unitIsoSelf_inv (X : C) :
    (MonoidalClosed.unitIsoSelf X).inv = MonoidalClosed.curry (λ_ X).hom := by
  have h := unit_conjugateEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).hom X
  dsimp at h
  erw [Category.id_comp] at h
  change (conjugateEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).hom).app X = _
  rw [h, MonoidalClosed.curry_eq]
  try rfl

theorem toBidual_comp_pre_app_comp_unitIsoSelf_hom {M : C} (ι : M ⟶ 𝟙_ C) :
    toBidual M ≫ (MonoidalClosed.pre (MonoidalClosed.curry' ι)).app (𝟙_ C) ≫
      (MonoidalClosed.unitIsoSelf (𝟙_ C)).hom = ι := by
  have hk : MonoidalClosed.uncurry
      (toBidual M ≫ (MonoidalClosed.pre (MonoidalClosed.curry' ι)).app (𝟙_ C)) = (λ_ M).hom ≫ ι := by
    rw [MonoidalClosed.uncurry_pre_app, toBidual, MonoidalClosed.uncurry_curry,
      BraidedCategory.braiding_naturality_left_assoc, MonoidalClosed.whiskerLeft_curry'_ihom_ev_app,
      ← Category.assoc, braiding_rightUnitor]
  have h2 : toBidual M ≫ (MonoidalClosed.pre (MonoidalClosed.curry' ι)).app (𝟙_ C) =
      ι ≫ (MonoidalClosed.unitIsoSelf (𝟙_ C)).inv := by
    rw [unitIsoSelf_inv, ← MonoidalClosed.curry_natural_left, leftUnitor_naturality, ← hk,
      MonoidalClosed.curry_uncurry]
  rw [← Category.assoc, h2, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end ZeroSchemeCanonMC

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules Scheme.IdealSheafData.le_def Scheme.IdealSheafData Scheme.Modules.zeroSchemeIdeal Scheme.Modules.dual Scheme.Modules.IsInvertible)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Hom Γ Modules.Hom.comp_app Modules.Hom Hom.comp_app Modules IdealSheafData.le_def IdealSheafData Modules.zeroSchemeIdeal Modules.dual Modules.IsInvertible)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (Hom.comp_app Hom ofUnitSection coeff coeffIdeal coeff_mem_coeffIdeal zeroSchemeIdeal zeroSchemeIdeal_le sectionDual dual IsInvertible ihomSectionsEquiv restrictUnitIso' IsInvertible.isIso_ev_app_and_isIso_curry_braiding_ev ofUnitSection_sectionDual_app)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open AlgebraicGeometry

namespace ZeroSchemeCanon

variable {X : Scheme.{u}}

theorem zeroSchemeIdeal_invModuleSection {I : X.IdealSheafData} (hI : I.IsInvertible) :
    zeroSchemeIdeal I.invModuleSection = I := by
  have hM : Scheme.Modules.IsInvertible I.invModule := hI.isInvertible_invModule
  haveI hj : IsIso (ZeroSchemeCanonMC.toBidual I.module) :=
    (hI.isInvertible_module.isIso_ev_app_and_isIso_curry_braiding_ev).2
  have hcomp : ZeroSchemeCanonMC.toBidual I.module ≫ sectionDual I.invModuleSection = I.moduleι :=
    ZeroSchemeCanonMC.toBidual_comp_pre_app_comp_unitIsoSelf_hom I.moduleι

  have hsd : sectionDual I.invModuleSection = inv (ZeroSchemeCanonMC.toBidual I.module) ≫ I.moduleι := by
    rw [← hcomp, IsIso.inv_hom_id_assoc]
  apply le_antisymm
  ·
    refine zeroSchemeIdeal_le fun U => ?_
    rw [coeffIdeal, Ideal.span_le]
    rintro _ ⟨φ, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : Γ(Scheme.Modules.dual I.invModule, U.1),
        ihomSectionsEquiv I.invModule (𝟙_ X.Modules) U.1 t = φ ≫ (restrictUnitIso' U.1.ι).inv :=
      ⟨_, AddEquiv.apply_symm_apply _ _⟩
    have hφ : coeff I.invModuleSection U.1 φ =
        ofUnitSection U.1 ((sectionDual I.invModuleSection).app U.1 t) := by
      rw [ofUnitSection_sectionDual_app, ht, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hmem : (sectionDual I.invModuleSection).app U.1 t ∈ Set.range (I.moduleι.app U) :=
      ⟨(inv (ZeroSchemeCanonMC.toBidual I.module)).app U.1 t, by rw [hsd]; rfl⟩
    rw [(I.range_moduleIota_app_and_injective U).1] at hmem
    rw [hφ]
    exact hmem
  ·
    rw [Scheme.IdealSheafData.le_def]
    intro U x hx
    have hx' : x ∈ Set.range (I.moduleι.app U) := by
      rw [(I.range_moduleIota_app_and_injective U).1]; exact hx
    obtain ⟨y, rfl⟩ := hx'
    have hy : (sectionDual I.invModuleSection).app U.1
        ((ZeroSchemeCanonMC.toBidual I.module).app U.1 y) = I.moduleι.app U.1 y := by
      change ((ZeroSchemeCanonMC.toBidual I.module).app U.1 ≫
        (sectionDual I.invModuleSection).app U.1) y = _
      rw [← Scheme.Modules.Hom.comp_app, hcomp]
    change ofUnitSection U.1 (I.moduleι.app U.1 y) ∈ (zeroSchemeIdeal I.invModuleSection).ideal U
    rw [← hy, ofUnitSection_sectionDual_app]
    exact (hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq _).1 U (coeff_mem_coeffIdeal _ U.1 _)

end ZeroSchemeCanon

end AlgebraicGeometry.Scheme.Modules
open _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection.AlgebraicGeometry

end

theorem solution
    {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) :
    Scheme.Modules.zeroSchemeIdeal I.invModuleSection = I :=
  AlgebraicGeometry.Scheme.Modules.ZeroSchemeCanon.zeroSchemeIdeal_invModuleSection hI
