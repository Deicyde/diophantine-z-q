import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative.lean
Original Git blob: 6891aef2664900cd85e6ac2e520fe78653f5d2c0
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 4 old-version global performance-guard attribute lines (no proof or type).
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative
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
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)).1) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
