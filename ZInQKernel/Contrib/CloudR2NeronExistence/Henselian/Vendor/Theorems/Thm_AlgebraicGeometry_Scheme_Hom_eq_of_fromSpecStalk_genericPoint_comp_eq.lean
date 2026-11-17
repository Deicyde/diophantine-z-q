import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq.lean
Original Git blob: 9049dc1312c7b954af905a980ccc65c4834d757e
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory TopologicalSpace"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Hom.eq_of_fromSpecStalk_genericPoint_comp_eq
    {U H S : Scheme.{u}} [IsIntegral U] (sU : U ⟶ S) (sH : H ⟶ S) [IsSeparated sH]
    (f g : U ⟶ H) (hf : f ≫ sH = sU) (hg : g ≫ sH = sU)
    (h : U.fromSpecStalk (genericPoint U) ≫ f = U.fromSpecStalk (genericPoint U) ≫ g) :
    f = g := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
