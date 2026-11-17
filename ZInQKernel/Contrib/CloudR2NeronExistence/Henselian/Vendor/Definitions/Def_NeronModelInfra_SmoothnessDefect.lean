import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Definitions/Def_NeronModelInfra_SmoothnessDefect.lean
Original Git blob: e1164a93748dce52bc1d57ff5c6406153967b45e
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 2 namespace-sensitive axiom-print diagnostics; full final AX3 audit is separate.
-/
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import Mathlib

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace NeronModelInfra
h77_bridge_namespace

def stalkAlgebraMap {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (x : X) : R →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem stalkAlgebraMap_apply {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) (r : R) :
    stalkAlgebraMap f x r =
      (X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) :=
  rfl

abbrev stalkAlgebra {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (x : X) : Algebra R (X.presheaf.stalk x) :=
  (stalkAlgebraMap f x).toAlgebra

abbrev pointAlgebra {X : Scheme.{u}} {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ X) :
    Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' :=
  (Scheme.stalkClosedPointTo a).hom.toAlgebra

def smoothnessDefect {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X) : ℕ∞ :=
  letI : Algebra R (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) :=
    stalkAlgebra f (a (IsLocalRing.closedPoint R'))
  letI : Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' := pointAlgebra a
  Module.length R'
    (Submodule.torsion R'
      (R' ⊗[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))]
        Ω[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))⁄R]))

theorem smoothnessDefect_def {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X) :
    smoothnessDefect f a =
      (letI : Algebra R (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) :=
        stalkAlgebra f (a (IsLocalRing.closedPoint R'))
      letI : Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' := pointAlgebra a
      Module.length R'
        (Submodule.torsion R'
          (R' ⊗[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))]
            Ω[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))⁄R]))) :=
  rfl

section Gate

variable (R : Type u) [CommRing R]

theorem stalkAlgebraMap_id (p : PrimeSpectrum R) :
    stalkAlgebraMap (𝟙 (Spec (CommRingCat.of R))) p = (StructureSheaf.toStalk R p).hom := by
  apply RingHom.ext
  intro r
  simp only [stalkAlgebraMap, Scheme.Hom.id_appTop, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_id, RingHom.id_apply, StructureSheaf.toStalk, CommRingCat.hom_comp,
    Scheme.ΓSpecIso_inv, CommRingCat.hom_ofHom]
  rfl

theorem smoothnessDefect_id {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) :
    smoothnessDefect (𝟙 (Spec (CommRingCat.of R))) a = 0 := by
  rw [smoothnessDefect_def]
  set p : PrimeSpectrum R := a (IsLocalRing.closedPoint R') with hp
  letI iRB : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk p) :=
    stalkAlgebra (𝟙 (Spec (CommRingCat.of R))) p
  letI : Algebra ((Spec (CommRingCat.of R)).presheaf.stalk p) R' := pointAlgebra a
  have hAlg : iRB = StructureSheaf.stalkAlgebra R p := by
    refine Algebra.algebra_ext _ _ fun r => ?_
    change stalkAlgebraMap (𝟙 (Spec (CommRingCat.of R))) p r = _
    rw [stalkAlgebraMap_id]
    rfl
  have hunr : @Algebra.FormallyUnramified R ((Spec (CommRingCat.of R)).presheaf.stalk p) _ _ iRB := by
    rw [hAlg]
    exact @Algebra.FormallyUnramified.of_isLocalization _ _ _ _ p.asIdeal.primeCompl _
      (StructureSheaf.IsLocalization.to_stalk R p)
  haveI : Subsingleton Ω[(Spec (CommRingCat.of R)).presheaf.stalk p⁄R] :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  haveI : Subsingleton
      (R' ⊗[(Spec (CommRingCat.of R)).presheaf.stalk p] Ω[(Spec (CommRingCat.of R)).presheaf.stalk p⁄R]) :=
    inferInstance
  exact Module.length_eq_zero

end Gate

end NeronModelInfra

end




end ZInQ.Contrib.CloudR2NeronExistence.Henselian
