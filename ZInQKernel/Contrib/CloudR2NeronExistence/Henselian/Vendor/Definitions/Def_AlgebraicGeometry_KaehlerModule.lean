import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Definitions/Def_AlgebraicGeometry_KaehlerModule.lean
Original Git blob: ffbc98ebe82fb22f61f8757bcbf6c6ab1849f51c
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 2 namespace-sensitive axiom-print diagnostics; full final AX3 audit is separate.
-/
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Hom
h77_bridge_namespace

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

def constToPresheaf : (Functor.const (X.Opens)ᵒᵖ).obj (CommRingCat.of A) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.unop le_top
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
    rw [Scheme.Hom.appLE_map]

@[reducible] def sectionsAlgebra (U : X.Opens) : Algebra A Γ(X, U) :=
  ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.constToPresheaf f).app (op U)).hom.toAlgebra

def kaehlerPresheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.constToPresheaf f)

def kaehler : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f)

def topDifferentials (d : ℕ) : X.Modules :=
  Scheme.Modules.det d (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f)

abbrev topPresheaf (d : ℕ) : X.PresheafOfModules :=
  (Scheme.Modules.presheafExteriorPower X d).obj (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f)

@[simp] lemma kaehlerPresheaf_obj (U : (X.Opens)ᵒᵖ) :
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj U = CommRingCat.KaehlerDifferential ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.constToPresheaf f).app U) := rfl

def kaehlerToSections (U : X.Opens) :
    ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op U) : Type u) → (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f)).app (op U)).hom s

def kaehlerToSectionsₗ (U : X.Opens) :
    ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op U)) →ₗ[Γ(X, U)] (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), U) : Type u) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f)).app (op U)).hom

def topToSections (d : ℕ) (U : X.Opens) :
    (⋀[Γ(X, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op U)) : Type u) → (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((Scheme.Modules.presheafExteriorPower X d).obj (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val)).app (op U)).hom
    (exteriorPower.map d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSectionsₗ f) U) s)

theorem kaehlerToSections_add (U : X.Opens) (s t : (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op U)) :
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) U (s + t) = (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) U s + (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) U t :=
  map_add ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSectionsₗ f) U) s t

theorem kaehlerPresheaf_nontrivial_polynomial (A : Type u) [CommRing A] [Nontrivial A] :
    letI f : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A (Polynomial A)))
    Nontrivial ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op ⊤)) := by
  set f : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Polynomial A))) with hf

  let Γ' : Type u := Γ(Spec (CommRingCat.of (Polynomial A)), ⊤)
  letI algA : Algebra A Γ' := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) ⊤
  let e : Γ' ≃+* Polynomial A := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).commRingCatIsoToRingEquiv
  letI : Algebra Γ' (Polynomial A) := e.toRingHom.toAlgebra

  have hcomp : (algebraMap Γ' (Polynomial A)).comp (algebraMap A Γ') = algebraMap A (Polynomial A) := by
    refine RingHom.ext fun a => ?_
    change (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).hom.hom
      ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = algebraMap A (Polynomial A) a
    have h1 : f.appLE ⊤ ⊤ le_top = f.appTop := by
      simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    rw [h1]
    have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A (Polynomial A)))
    rw [← hf] at h2
    have h3 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) h2
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
    rw [h3]
    change algebraMap A (Polynomial A) (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom a) = _
    rw [Iso.inv_hom_id]; rfl
  haveI : IsScalarTower A Γ' (Polynomial A) := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hsurj : Function.Surjective (KaehlerDifferential.map A A Γ' (Polynomial A)) :=
    KaehlerDifferential.map_surjective_of_surjective A A (h := e.surjective)
  haveI : Nontrivial (Ω[Polynomial A⁄A]) :=
    (KaehlerDifferential.polynomialEquiv A).toEquiv.nontrivial
  exact hsurj.nontrivial

end AlgebraicGeometry.Scheme.Hom

end

end ZInQ.Contrib.CloudR2NeronExistence.Henselian
