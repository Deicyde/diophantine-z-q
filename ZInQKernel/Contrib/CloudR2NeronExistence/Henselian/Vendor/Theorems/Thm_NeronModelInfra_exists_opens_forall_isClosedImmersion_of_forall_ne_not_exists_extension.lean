import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension.lean
Original Git blob: bfe2fed0f8dad411f53dcef0596cc0e4f4321b53
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 1 old-version global performance-guard attribute lines (no proof or type).
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension

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

open CategoryTheory CategoryTheory.Limits open ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry hiding exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType open NeronModelInfra

universe u

theorem NeronModelInfra.exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {ι : Type u} [Finite ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, Smooth (f i) ∧ IsSeparated (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i))
    (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i, IsIso (e i).1)
    (ξ : ∀ i, ↥(Y i)) (hξ : ∀ i, (f i).base (ξ i) = IsLocalRing.closedPoint R)
    (hξgen : ∀ i (y : ↥(Y i)), (f i).base y = IsLocalRing.closedPoint R → ξ i ⤳ y)
    (hne : ∀ i j, i ≠ j → ∀ (U : (Y i).Opens), ξ i ∈ U → ∀ u : SchemeHomOver (U.ι ≫ f i) (f j),
      (genericFibreRestrict R K (f j) (U.ι ≫ f i) u).1 ≫ (e j).1 ≠
        (genericFibreRestrict R K (f i) (U.ι ≫ f i) ⟨U.ι, rfl⟩).1 ≫ (e i).1) :
    ∃ V : ∀ i, (Y i).Opens,
      (∀ i, ξ i ∈ V i) ∧
      (∀ i (y : ↥(Y i)), (f i).base y ≠ IsLocalRing.closedPoint R → y ∈ V i) ∧
      (∀ i, IsIso (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1) ∧
      ∀ i j, i ≠ j →
        ∀ δ : pullback
              (schemeHomOverComp (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩) (e i)).1
              (schemeHomOverComp (genericFibreRestrict R K (f j) ((V j).ι ≫ f j) ⟨(V j).ι, rfl⟩) (e j)).1 ⟶
            pullback ((V i).ι ≫ f i) ((V j).ι ≫ f j),
          δ ≫ pullback.fst ((V i).ι ≫ f i) ((V j).ι ≫ f j) =
            pullback.fst _ _ ≫ pullback.fst ((V i).ι ≫ f i) (specGenericFibreInclusion R K) →
          δ ≫ pullback.snd ((V i).ι ≫ f i) ((V j).ι ≫ f j) =
            pullback.snd _ _ ≫ pullback.fst ((V j).ι ≫ f j) (specGenericFibreInclusion R K) →
          IsClosedImmersion δ := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
