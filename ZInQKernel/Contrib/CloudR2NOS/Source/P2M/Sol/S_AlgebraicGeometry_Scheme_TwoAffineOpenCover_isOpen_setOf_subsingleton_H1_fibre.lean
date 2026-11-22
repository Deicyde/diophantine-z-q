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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isOpen_setOf_subsingleton_H1_fibre.lean
  Source sha256  : bc8321c5c0406cea854f86244b50dbad6297914a80f5bb7218d84d53af5afd56
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 4 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 9 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T6×1; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_LinearMap_isOpen_setOf_surjective_baseChange_residueField
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isOpen_setOf_subsingleton_H1_fibre
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
r2nos_erase_attr "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
r2nos_erase_attr "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq"
r2nos_erase_attr "simp" "AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"

namespace K4Geom
r2nos_namespace_dual

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

universe u

theorem nonempty_cokerBaseChangeEquiv {R : Type*} [CommRing R] {C0 C1 : Type*} [AddCommGroup C0] [Module R C0]
    [AddCommGroup C1] [Module R C1] (d : C0 →ₗ[R] C1) (K : Type*) [CommRing K] [Algebra R K] :
    Nonempty (((K ⊗[R] C1) ⧸ LinearMap.range (d.baseChange K)) ≃ₗ[K] K ⊗[R] (C1 ⧸ LinearMap.range d)) := by
  let q : C1 →ₗ[R] C1 ⧸ LinearMap.range d := (LinearMap.range d).mkQ
  let qK : K ⊗[R] C1 →ₗ[K] K ⊗[R] (C1 ⧸ LinearMap.range d) := q.baseChange K
  have hsurj : Function.Surjective qK := by
    rw [show (qK : K ⊗[R] C1 → K ⊗[R] (C1 ⧸ LinearMap.range d)) = LinearMap.lTensor K q from
      LinearMap.baseChange_eq_ltensor q]
    exact LinearMap.lTensor_surjective K (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker qK = LinearMap.range (d.baseChange K) := by
    have h1 : LinearMap.ker (LinearMap.lTensor K q) = LinearMap.range (LinearMap.lTensor K d) := by
      rw [lTensor_mkQ]
      have hd : d = (LinearMap.range d).subtype ∘ₗ d.rangeRestrict := LinearMap.ext fun _ => rfl
      conv_rhs => rw [hd, LinearMap.lTensor_comp]
      rw [LinearMap.range_comp_of_range_eq_top]
      exact LinearMap.range_eq_top.mpr (LinearMap.lTensor_surjective K (LinearMap.surjective_rangeRestrict d))
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    have hx : qK x = LinearMap.lTensor K q x := congrFun (LinearMap.baseChange_eq_ltensor q) x
    rw [hx, ← LinearMap.mem_ker, h1, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor d) y)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor d) y).symm⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (qK.quotKerEquivOfSurjective hsurj)⟩

theorem surjective_baseChange_iff {R : Type*} [CommRing R] {C0 C1 : Type*} [AddCommGroup C0] [Module R C0]
    [AddCommGroup C1] [Module R C1] (d : C0 →ₗ[R] C1) (K : Type*) [CommRing K] [Algebra R K] :
    Function.Surjective (d.baseChange K) ↔ Subsingleton (K ⊗[R] (C1 ⧸ LinearMap.range d)) := by
  obtain ⟨e⟩ := nonempty_cokerBaseChangeEquiv d K
  rw [← e.toEquiv.subsingleton_congr, Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A)) [IsProper c]
  (𝒱 : C.TwoAffineOpenCover) (M : C.Modules) (hM : Scheme.Modules.IsInvertible M)

include hM in

theorem finite_H1 : Module.Finite A (𝒱.sectionsOf c M).H1 := by
  have hcf := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial c M hM.1 𝒱.toOrderedAffineCover
  exact ((OModulePresheaf.cechFinite_toOrderedAffineCover_iff _ _).mp hcf).2

include hM in
theorem iff_pair (𝔭 : PrimeSpectrum A) :
    (Subsingleton
        ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1 ↔
      Function.Surjective ((𝒱.sectionsOf c M).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) ∧
    (Subsingleton
        ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1 ↔
      𝔭 ∉ Module.support A (𝒱.sectionsOf c M).H1) := by
  obtain ⟨⟨eH1⟩, -, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 c M hM.1 𝔭.asIdeal.ResidueField
  have e1 : Subsingleton ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1 ↔ Subsingleton (𝔭.asIdeal.ResidueField ⊗[A] (𝒱.sectionsOf c M).H1) :=
    eH1.toEquiv.subsingleton_congr
  haveI := finite_H1 c 𝒱 M hM
  refine ⟨e1.trans (surjective_baseChange_iff _ _).symm, e1.trans ?_⟩
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]

include hM in
theorem isOpen :
    IsOpen {𝔭 : PrimeSpectrum A | Subsingleton
      ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1} := by
  haveI := finite_H1 c 𝒱 M hM
  have h : {𝔭 : PrimeSpectrum A | Subsingleton ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1} =
      {𝔭 : PrimeSpectrum A | Function.Surjective ((𝒱.sectionsOf c M).cechDiff.baseChange 𝔭.asIdeal.ResidueField)} := by
    ext 𝔭
    exact (iff_pair c 𝒱 M hM 𝔭).1
  rw [h]
  exact LinearMap.isOpen_setOf_surjective_baseChange_residueField _

end K4Geom

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct _root_.AlgebraicGeometry _root_.TensorProduct in
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct" in

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A)) [IsProper c]
    (𝒱 : C.TwoAffineOpenCover) (M : C.Modules) (hM : Scheme.Modules.IsInvertible M) :
    IsOpen {𝔭 : PrimeSpectrum A | Subsingleton
      ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1} :=
  K4Geom.isOpen c 𝒱 M hM
end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isOpen_setOf_subsingleton_H1_fibre
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
