import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_exteriorPower_exists_linearEquiv_baseChange.lean
Original Git blob: 7a086fc994ca8d3785c8296cf3f0a7906207a624
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_exteriorPower_exists_linearEquiv_baseChange

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
/- Source package leanOptions restored for this direct compiler leaf; no config edit. -/
set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

h77_open "TensorProduct"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

open scoped _root_.TensorProduct

theorem exteriorPower.exists_linearEquiv_baseChange
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    ∃ e : A ⊗[R] (⋀[R]^n M) ≃ₗ[A] ⋀[A]^n (A ⊗[R] M),
      ∀ (a : A) (m : Fin n → M),
        e (a ⊗ₜ exteriorPower.ιMulti R n m) =
          a • exteriorPower.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] m i) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_exteriorPower_exists_linearEquiv_baseChange.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
