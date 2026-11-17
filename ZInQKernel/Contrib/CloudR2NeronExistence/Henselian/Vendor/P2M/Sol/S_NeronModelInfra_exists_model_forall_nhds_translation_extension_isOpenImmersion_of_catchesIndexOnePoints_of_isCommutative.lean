import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_NeronModelInfra_exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative.lean
Original Git blob: 293447321c79093eff677839e7da71ee6e29f46e
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 2 old-version global performance-guard attribute lines (no proof or type).
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_exists_model_openCover_of_forall_ne_not_exists_extension
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK) (hcomm : LXK.IsCommutative)
    (M : ModelFamily R K gK) (hfin : Finite M.ι)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
      (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK),
      Smooth f ∧ IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
      (∃ x : X, f.base x = IsLocalRing.closedPoint R) ∧ IsIso e.1 ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
          IsOpenImmersion
            (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
              ((Category.assoc _ _ _).trans τ.2.symm)) ∧
          (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
            pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1) ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
          IsOpenImmersion
            (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
              ((Category.assoc _ _ _).trans τ.2.symm)) ∧
          (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
            pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)).1) := by
  classical

  obtain ⟨d, hd⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth LXK
  obtain ⟨ω, hωframe, hleft⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq gK LXK d

  obtain ⟨D, hD⟩ :=
    NeronModelInfra.exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints K LXK M hfin hM hpts d ω
      hωframe

  obtain ⟨X, g, eX, V, j, hsm, hsep, hlft, hqc, hiso, hyV, hVK, hjopen, hjchart, hcover⟩ :=
    NeronModelInfra.exists_model_openCover_of_forall_ne_not_exists_extension K gK
      (fun c => (D.C c).Y) (fun c => (D.C c).f)
      (fun c => ⟨(D.C c).smooth, D.isSeparated c, (D.C c).locallyOfFiniteType, D.quasiCompact c⟩)
      (fun c => (D.C c).e) D.isIso (fun c => (D.C c).y) (fun c => (D.C c).hy) D.hgen D.inequiv

  obtain ⟨hL, hR⟩ :=
    NeronModelInfra.forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative
      K LXK hcomm M hM hpts d ω hωframe hleft D hD X g eX V j hyV hVK hjopen hjchart hcover
  obtain ⟨c₀⟩ := D.nonempty
  refine ⟨X, g, eX, hsm, hsep, hlft, hqc, ⟨(j c₀).1.base ⟨(D.C c₀).y, hyV c₀⟩, ?_⟩, hiso, hL, hR⟩

  have h2 := congrArg (fun φ => φ.base ⟨(D.C c₀).y, hyV c₀⟩) (j c₀).2
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
  exact h2.trans (D.C c₀).hy


end P2MW.S_NeronModelInfra_exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
