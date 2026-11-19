import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd.lean
Original Git blob: 675dee797760f96faebbf559dafd552707224a93
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isIso_lift_baseChange_fst_baseChange_snd
    {S S' Z X : Scheme.{u}} (z : Z ⟶ S) (f : X ⟶ S) (ι : S' ⟶ S) :
    IsIso
      (pullback.lift
        (pullback.lift (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.fst z f)
          (pullback.snd (pullback.fst z f ≫ z) ι)
          (by rw [Category.assoc]; exact pullback.condition))
        (pullback.lift (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.snd z f)
          (pullback.snd (pullback.fst z f ≫ z) ι)
          (by rw [Category.assoc, ← pullback.condition (f := z) (g := f)]; exact pullback.condition))
        (by rw [pullback.lift_snd, pullback.lift_snd]) :
        pullback (pullback.fst z f ≫ z) ι ⟶ pullback (pullback.snd z ι) (pullback.snd f ι)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
