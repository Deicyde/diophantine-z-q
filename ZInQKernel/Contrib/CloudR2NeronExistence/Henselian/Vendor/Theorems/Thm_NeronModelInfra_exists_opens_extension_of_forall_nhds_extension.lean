import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_opens_extension_of_forall_nhds_extension.lean
Original Git blob: 1350d4d52c07caddfdc7da4e9da729a873732322
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.SharedDiagnostics
import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_opens_extension_of_forall_nhds_extension

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

h77_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~genericFibreRestrict_injective_of_flat_of_isSeparated"

theorem NeronModelInfra.exists_opens_extension_of_forall_nhds_extension
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (hloc : ∀ η : T, t.base η = IsLocalRing.closedPoint R →
      (∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : T.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ t) f),
        (genericFibreRestrict R K f (U.ι ≫ t) g).1 =
          pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1) :
    ∃ (V : T.Opens) (v : SchemeHomOver (V.ι ≫ t) f),
      (∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      (∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V) ∧
      (genericFibreRestrict R K f (V.ι ≫ t) v).1 =
        pullback.map (V.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) V.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_opens_extension_of_forall_nhds_extension.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
