import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_NeronModelInfra_exists_model_openCover_of_forall_ne_not_exists_extension.lean
Original Git blob: 42a66fb01e5b2dfdbd030a045791e72d189d6e9e
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 1 old-version global performance-guard attribute lines (no proof or type).
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_exists_model_openCover_of_forall_ne_not_exists_extension
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {ι : Type u} [Finite ι] [Nonempty ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, Smooth (f i) ∧ IsSeparated (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i))
    (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i, IsIso (e i).1)
    (ξ : ∀ i, ↥(Y i)) (hξ : ∀ i, (f i).base (ξ i) = IsLocalRing.closedPoint R)
    (hξgen : ∀ i (y : ↥(Y i)), (f i).base y = IsLocalRing.closedPoint R → ξ i ⤳ y)
    (hne : ∀ i j, i ≠ j → ∀ (U : (Y i).Opens), ξ i ∈ U → ∀ u : SchemeHomOver (U.ι ≫ f i) (f j),
      (genericFibreRestrict R K (f j) (U.ι ≫ f i) u).1 ≫ (e j).1 ≠
        (genericFibreRestrict R K (f i) (U.ι ≫ f i) ⟨U.ι, rfl⟩).1 ≫ (e i).1) :
    ∃ (X : Scheme.{u}) (g : X ⟶ Spec (CommRingCat.of R))
      (eX : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK)
      (V : ∀ i, (Y i).Opens) (j : ∀ i, SchemeHomOver ((V i).ι ≫ f i) g),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧ IsIso eX.1 ∧
      (∀ i, ξ i ∈ V i) ∧
      (∀ i (y : ↥(Y i)), (f i).base y ≠ IsLocalRing.closedPoint R → y ∈ V i) ∧
      (∀ i, IsOpenImmersion (j i).1) ∧
      (∀ i, (genericFibreRestrict R K g ((V i).ι ≫ f i) (j i)).1 ≫ eX.1 =
        (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1 ≫ (e i).1) ∧
      (∀ x : ↥X, ∃ i, x ∈ Set.range (j i).1.base) := by
  obtain ⟨V, hξV, hgen, hiso, hdiag⟩ :=
    NeronModelInfra.exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension
      K gK Y f hf e he ξ hξ hξgen hne

  have hf' : ∀ i, Smooth ((V i).ι ≫ f i) ∧ IsSeparated ((V i).ι ≫ f i) ∧
      LocallyOfFiniteType ((V i).ι ≫ f i) ∧ QuasiCompact ((V i).ι ≫ f i) := by
    intro i
    obtain ⟨h1, h2, h3, h4⟩ := hf i
    haveI : IsLocallyNoetherian (Y i) := LocallyOfFiniteType.isLocallyNoetherian (f i)
    haveI : CompactSpace ↥(Y i) := QuasiCompact.compactSpace_of_compactSpace (f i)
    haveI : IsNoetherian (Y i) := {}
    haveI : TopologicalSpace.NoetherianSpace ↥(V i : Scheme.{u}) :=
      (inferInstance : TopologicalSpace.NoetherianSpace (V i : Set ↥(Y i)))
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have he' : ∀ i, IsIso (schemeHomOverComp
      (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩) (e i)).1 := by
    intro i
    haveI := hiso i
    haveI := he i
    show IsIso ((genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1 ≫ (e i).1)
    infer_instance
  obtain ⟨X, g, eX, j, hsm, hsep, hlft, hqc, hiX, hopen, hcomp, hcov⟩ :=
    NeronModelInfra.exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
      K gK (fun i => (V i : Scheme.{u})) (fun i => (V i).ι ≫ f i) hf'
      (fun i => schemeHomOverComp (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩) (e i))
      he' hdiag
  exact ⟨X, g, eX, V, j, hsm, hsep, hlft, hqc, hiX, hξV, hgen, hopen, hcomp, hcov⟩


end P2MW.S_NeronModelInfra_exists_model_openCover_of_forall_ne_not_exists_extension
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
