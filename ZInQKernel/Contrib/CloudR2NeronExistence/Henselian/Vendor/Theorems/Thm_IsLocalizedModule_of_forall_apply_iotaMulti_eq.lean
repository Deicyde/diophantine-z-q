import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_IsLocalizedModule_of_forall_apply_iotaMulti_eq.lean
Original Git blob: 4e2ae27bfc520f8ce747b2f4c4e94d6699e10139
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_IsLocalizedModule_of_forall_apply_iotaMulti_eq

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "TensorProduct"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem IsLocalizedModule.of_forall_apply_iotaMulti_eq
    {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (n : ℕ)
    (F : ⋀[R]^n M →ₗ[R] ⋀[A]^n N)
    (hF : ∀ m : Fin n → M, F (exteriorPower.ιMulti R n m) = exteriorPower.ιMulti A n (fun i => f (m i))) :
    IsLocalizedModule S F := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_IsLocalizedModule_of_forall_apply_iotaMulti_eq.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
