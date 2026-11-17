import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict.lean
Original Git blob: 80f7580ba885091eaadeb4a03457198742f78eba
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict

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

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict
    {U W : Scheme.{u}} (v : U ⟶ W) (u : U)
    [IsDomain (U.presheaf.stalk u)] [IsDomain (W.presheaf.stalk (v.base u))]
    (U' : U.Opens) [IsOpenImmersion (U'.ι ≫ v)] (hU' : ∃ x : U, x ∈ U' ∧ x ⤳ u) :
    letI : Algebra (W.presheaf.stalk (v.base u)) (FractionRing (U.presheaf.stalk u)) :=
      ((algebraMap (U.presheaf.stalk u) (FractionRing (U.presheaf.stalk u))).comp (v.stalkMap u).hom).toAlgebra
    IsFractionRing (W.presheaf.stalk (v.base u)) (FractionRing (U.presheaf.stalk u)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
