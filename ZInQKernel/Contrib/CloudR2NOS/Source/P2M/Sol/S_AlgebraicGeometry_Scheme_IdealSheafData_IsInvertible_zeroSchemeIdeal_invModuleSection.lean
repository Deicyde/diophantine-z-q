/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection.lean
  Source sha256  : b063b10ea93277a9d9e0b4229566616b23cc26f2ea79f0691343f32021e38d05
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 6 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 6 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 10 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_and_isIso_curry_braiding_ev
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ofUnitSection_sectionDual_app
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
r2nos_namespace_dual
r2nos_erase_attr "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
r2nos_erase_attr "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection.AlgebraicGeometry"

noncomputable section

namespace ZeroSchemeCanonMC
r2nos_namespace_dual

w03_open "CategoryTheory.MonoidalClosed"

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
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules Scheme.IdealSheafData.le_def Scheme.IdealSheafData Scheme.Modules.zeroSchemeIdeal Scheme.Modules.dual Scheme.Modules.IsInvertible"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "Hom Γ Modules.Hom.comp_app Modules.Hom Hom.comp_app Modules IdealSheafData.le_def IdealSheafData Modules.zeroSchemeIdeal Modules.dual Modules.IsInvertible"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "Hom.comp_app Hom ofUnitSection coeff coeffIdeal coeff_mem_coeffIdeal zeroSchemeIdeal zeroSchemeIdeal_le sectionDual dual IsInvertible ihomSectionsEquiv restrictUnitIso' IsInvertible.isIso_ev_app_and_isIso_curry_braiding_ev ofUnitSection_sectionDual_app"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace ZeroSchemeCanon
r2nos_namespace_dual

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

end

theorem solution
    {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) :
    Scheme.Modules.zeroSchemeIdeal I.invModuleSection = I :=
  AlgebraicGeometry.Scheme.Modules.ZeroSchemeCanon.zeroSchemeIdeal_invModuleSection hI
end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
