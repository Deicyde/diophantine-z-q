import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing.lean
Original Git blob: 6a2b446e682b9396cda01796aab7f43926d4e7ea
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 5 old-version global performance-guard attribute lines (no proof or type).
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_neronModelPropertyBundle_of_forall_nhds_twist_extension
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isCommutative_genericFibre
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.ModelFamilySmoothening
/- NOTICE OF MODIFICATION: the original ordinary-DVR F1H9 smooth-model-family
helper block is moved to ModelFamilySmoothening under its same full namespace;
no hypothesis/output/proof content weakened and no duplicate declaration. -/

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace F1H9
h77_bridge_namespace

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)}

/- Ordinary-DVR gfMap and exists_smooth_modelFamily are moved to
ModelFamilySmoothening.lean under this SAME namespace; no duplicate declaration. -/

theorem isCommutative_genericFibre
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g) (LAK : RelativeGroupLaw K gK)
    (hc : LAK.IsCommutative)
    (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (hemul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
      NeronModelInfra.schemeHomOverComp (((ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.RelativeGroupLaw.genericFibre K LB)).mul t x y) e =
        LAK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e)) :
    ((ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.RelativeGroupLaw.genericFibre K LB)).IsCommutative := by
  intro T t x y
  have h := hemul t x y
  rw [hc, ← hemul t y x] at h
  apply Subtype.ext
  rw [← cancel_mono e.1]
  exact congrArg (fun s => s.1) h

end F1H9

open F1H9 in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)} (LAK : RelativeGroupLaw K gK)
    (hAK : AbelianSchemePropertyBundle K gK) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
      NeronModelPropertyBundle R K g ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
        LB.mul t x y = LB.mul t y x) ∧
      IsIso e.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp (((ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.RelativeGroupLaw.genericFibre K LB)).mul t x y) e =
          LAK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e)) := by
  haveI : IsProper gK := hAK.proper
  haveI : Smooth gK := hAK.smooth
  haveI : GeometricallyIntegral gK := hAK.geometricallyIntegral
  have hc : LAK.IsCommutative :=
    GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isProper_of_geometricallyIntegral LAK
  obtain ⟨M₀, hfin₀, hM₀, hpts₀⟩ :=
    NeronModelInfra.exists_modelFamily_finite_catchesIndexOnePoints_of_isProper (R := R) K gK
  obtain ⟨M, hfin, hM, hpts⟩ := exists_smooth_modelFamily K M₀ hfin₀
    (fun i => ⟨(hM₀ i).2.1, (hM₀ i).2.2.2.1, (hM₀ i).2.2.2.2⟩) hpts₀
  obtain ⟨B, g, LB, e, hsm, hsep, hloft, hqc, he, hemul, htw⟩ :=
    NeronModelInfra.exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative
      (R := R) K LAK hc M hfin hM hpts
  haveI := hsm; haveI := hsep; haveI := hloft; haveI := hqc; haveI := he
  refine ⟨B, g, LB, e, ?_, ?_, he, hemul⟩
  · exact NeronModelInfra.neronModelPropertyBundle_of_forall_nhds_twist_extension K LB htw
  · have hgen : ((ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.RelativeGroupLaw.genericFibre K LB)).IsCommutative := isCommutative_genericFibre K LB LAK hc e hemul
    have hLB : LB.IsCommutative :=
      GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isCommutative_genericFibre K LB hgen
    intro T t x y
    exact hLB t x y


end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
