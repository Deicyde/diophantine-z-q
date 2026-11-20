import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_DescentAction_effective_of_finiteEtale.lean
Original Git blob: d02377707f9674e1dddf069653e3f13c101ad559
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_DescentAction
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
/- Source package leanOptions restored for this direct compiler leaf; no config edit. -/
set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.DescentAction.effective_of_finiteEtale
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X' : Scheme.{u}} {x' : X' ⟶ Spec (CommRingCat.of R')}
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) x')
    (haff : ∀ S : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    A.Effective := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
