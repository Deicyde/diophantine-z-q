import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem.lean
Original Git blob: 9a4aa29815e45f0923383541c6a3386d9a5f283f
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_opens_forall_mul_base_mem_of_forall_specializes_mem
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (S : Finset B) :
    ∃ Z : B.Opens, (∃ z : B, z ∈ Z ∧ g.base z = IsLocalRing.closedPoint R) ∧
      ∀ z : B, z ∈ Z → g.base z = IsLocalRing.closedPoint R →
      ∀ (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
        [Module.Finite R R']
        (γ : Spec (CommRingCat.of R') ⟶ B) (hγ : γ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R R'))),
        γ.base (IsLocalRing.closedPoint R') = z →
      ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ B)
        (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R'))
        (hx : x ≫ g = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))),
        x.base (IsLocalRing.closedPoint K) ∈ S →
        (LB.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
            (schemeHomOverComp t rfl (⟨γ, hγ⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g))
            ⟨x, hx⟩).1.base (IsLocalRing.closedPoint K) ∈ U := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
