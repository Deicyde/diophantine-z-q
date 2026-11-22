import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_TopFormOrder_addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer.lean
Original Git blob: 457c48ee2500a80b88e7be5e8a91c4c04f08db57
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_TopFormOrder_addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer

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

universe u

open NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (L : Type u) [Field L] [Algebra O L] [IsFractionRing O L] :
    (∀ a b : L, a ≠ 0 → b ≠ 0 → addOrd O L (a * b) = addOrd O L a + addOrd O L b) ∧
    (∀ x : O, 0 ≤ addOrd O L (algebraMap O L x)) ∧
    (∀ x : O, x ≠ 0 → (addOrd O L (algebraMap O L x) = 0 ↔ IsUnit x)) ∧
    (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R' O]
      [IsLocalHom (algebraMap R' O)],
      Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O →
      ∀ π : R', IsLocalRing.maximalIdeal R' = Ideal.span {π} →
        addOrd O L (algebraMap O L (algebraMap R' O π)) = 1) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_TopFormOrder_addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
