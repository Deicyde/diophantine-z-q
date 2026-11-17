import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing.lean
Original Git blob: eb19c24d3a06a70b3c8aba9bd71ad42b75edac17
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing

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

theorem AlgebraicGeometry.exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing
    {U W : Scheme.{u}} (v : U ⟶ W) [LocallyOfFiniteType v] [IsLocallyNoetherian W]
    (x : U) [IsDomain (U.presheaf.stalk x)] [IsDiscreteValuationRing (U.presheaf.stalk x)]
    (π : W.presheaf.stalk (v.base x)) (hπ0 : π ≠ 0) (hπ : (Ideal.span {π}).IsPrime)
    (hfrac : letI : Algebra (W.presheaf.stalk (v.base x)) (FractionRing (U.presheaf.stalk x)) :=
        ((algebraMap (U.presheaf.stalk x) (FractionRing (U.presheaf.stalk x))).comp (v.stalkMap x).hom).toAlgebra
      IsFractionRing (W.presheaf.stalk (v.base x)) (FractionRing (U.presheaf.stalk x)))
    (hfs : letI : Algebra (W.presheaf.stalk (v.base x)) (U.presheaf.stalk x) := (v.stalkMap x).hom.toAlgebra
      Algebra.FormallySmooth (W.presheaf.stalk (v.base x)) (U.presheaf.stalk x)) :
    ∃ V : U.Opens, x ∈ V ∧ IsOpenImmersion (V.ι ≫ v) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
