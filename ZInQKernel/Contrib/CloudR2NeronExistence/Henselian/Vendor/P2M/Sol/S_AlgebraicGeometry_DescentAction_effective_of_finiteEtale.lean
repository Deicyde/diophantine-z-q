import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale.lean
Original Git blob: c28e00b9fa745f8566f45d53659edf0c2b915662
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_DescentAction
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem solution
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X' : Scheme.{u}} {x' : X' ⟶ Spec (CommRingCat.of R')}
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) x')
    (haff : ∀ S : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    A.Effective := by
  classical

  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (by
      change RingHom.Flat (algebraMap R R'); exact RingHom.flat_algebraMap_iff.2 inferInstance)
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (IsFinite.SpecMap_iff _).2 (by change (algebraMap R R').Finite; exact RingHom.finite_algebraMap.mpr inferInstance)
  have hlofp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 (by
      change (algebraMap R R').FinitePresentation
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance)
  haveI := hflat; haveI := hfin; haveI := hlofp

  haveI : IsFinite (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := MorphismProperty.pullback_fst _ _ hfin
  haveI : Flat (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := MorphismProperty.pullback_fst _ _ hflat
  haveI : LocallyOfFinitePresentation (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := MorphismProperty.pullback_fst _ _ hlofp
  haveI : IsFinite A.act := by rw [A.act_eq_invol_fst]; infer_instance
  haveI : Flat A.act := by rw [A.act_eq_invol_fst]; infer_instance
  haveI : LocallyOfFinitePresentation A.act := by rw [A.act_eq_invol_fst]; infer_instance

  have haff' : ∀ x : X', ∃ U : X'.Opens, IsAffineOpen U ∧
      ∀ r : ↑(pullback (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
        (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))) r = x → A.act r ∈ U := by
    intro x
    have hfinite := (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))).finite_preimage_singleton x
    obtain ⟨U, hU, hSU⟩ := haff ((hfinite.image fun r => A.act r).toFinset)
    exact ⟨U, hU, fun r hr => hSU _ (by
      rw [Set.Finite.mem_toFinset]; exact ⟨r, by simpa using hr, rfl⟩)⟩

  obtain ⟨Y, p, w, _, hpflat, _, hpsurj, hR, ⟨hcolim⟩⟩ :=
    AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))) A.act
      (fun a b h₁ h₂ => A.hom_ext h₁ h₂) (fun T => A.equivalence T) haff'
  haveI := hpflat; haveI := hpsurj
  haveI : QuasiCompact p := inferInstance

  have hco : pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫ x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) =
      A.act ≫ x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [pullback.condition, reassoc_of% A.act_comp]
  obtain ⟨f, hpf⟩ := Cofork.IsColimit.desc' hcolim (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) hco

  obtain ⟨e, he, -, hc⟩ := AlgebraicGeometry.DescentAction.effective_of_isPullback_of_flat_surjective
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))) A p w hR f hpf
  exact ⟨Y, f, e, he, hc⟩


end P2MW.S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
