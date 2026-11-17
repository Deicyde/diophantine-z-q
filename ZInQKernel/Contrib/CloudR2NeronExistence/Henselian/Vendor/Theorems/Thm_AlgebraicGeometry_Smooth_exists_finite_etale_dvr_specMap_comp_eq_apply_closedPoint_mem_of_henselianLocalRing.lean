import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing.lean
Original Git blob: a53df93eb7ed0f8963976c2f25b0ea2fbcbefaeb
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (V : X.Opens) (x : X) (hx : f.base x = IsLocalRing.closedPoint R) (hxV : x ∈ V) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : HenselianLocalRing R')
      (a : Spec (CommRingCat.of R') ⟶ X),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' ∧
      a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ∧
      a.base (IsLocalRing.closedPoint R') ∈ V := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
