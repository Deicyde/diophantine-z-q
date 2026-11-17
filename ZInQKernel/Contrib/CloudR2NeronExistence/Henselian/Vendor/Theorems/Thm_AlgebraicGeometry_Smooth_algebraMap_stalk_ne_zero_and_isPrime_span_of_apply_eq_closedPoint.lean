import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint.lean
Original Git blob: 04e506ec8d579c85ec1e43e00a35cd8bd7a3e867
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 1 old-version global performance-guard attribute lines (no proof or type).
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry hiding isIntegral_of_smooth_of_preconnectedSpace

universe u

theorem AlgebraicGeometry.Smooth.algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (p : Y) (hp : f.base p = IsLocalRing.closedPoint R)
    [Algebra R (Y.presheaf.stalk p)]
    (halg : Y.fromSpecStalk p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk p)))) :
    algebraMap R (Y.presheaf.stalk p) ϖ ≠ 0 ∧
      (Ideal.span {algebraMap R (Y.presheaf.stalk p) ϖ}).IsPrime := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
