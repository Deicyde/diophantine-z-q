import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral.lean
Original Git blob: 9aa333d51635edda045f5a119730291c456d0776
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
/- Source package leanOptions restored for this direct compiler leaf; no config edit. -/
set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral
h77_bridge_namespace

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} [IsProper f]
    [GeometricallyIntegral f] (G : RelativeGroupLaw K f) : G.IsCommutative :=
  fun {_} t x y => (ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.RelativeGroupLaw.mul_comm_of_isProper_of_geometricallyIntegral G) t x y


end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
