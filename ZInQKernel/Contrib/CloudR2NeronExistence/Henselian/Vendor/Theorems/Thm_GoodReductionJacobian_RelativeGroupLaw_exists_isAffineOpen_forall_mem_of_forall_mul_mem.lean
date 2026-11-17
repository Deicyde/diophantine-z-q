import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem.lean
Original Git blob: 9ebe1cb5ca04945edcc705b3fc4d8e8de72f2191
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem

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

h77_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective NeronModelInfra GoodReductionJacobian"

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_forall_mul_mem
    {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    {T : Scheme.{u}} (t₁ : T ⟶ Spec (CommRingCat.of R))
    [IsFinite t₁] [Flat t₁] [LocallyOfFinitePresentation t₁] [Surjective t₁]
    (γ : SchemeHomOver t₁ g) (U : B.Opens) (hU : IsAffineOpen U) (S : Finset B)
    (hS : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ B) (t : Spec (CommRingCat.of K) ⟶ T)
      (hx : x ≫ g = t ≫ t₁), x.base (IsLocalRing.closedPoint K) ∈ S →
      (LB.mul (t ≫ t₁) (schemeHomOverComp t rfl γ) ⟨x, hx⟩).1.base (IsLocalRing.closedPoint K) ∈ U) :
    ∃ V : B.Opens, IsAffineOpen V ∧ ∀ b ∈ S, b ∈ V := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
