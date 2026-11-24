import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_TopFormOrder_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top.lean
Original Git blob: 2c8ba119e4d87a65966c999388c25aa5a2e61bf4
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_TopFormOrder_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top

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

open NeronModelInfra TopFormOrder

universe u

theorem NeronModelInfra.TopFormOrder.exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top
    (R K B B' O : Type u) [CommRing R] [CommRing K] [Algebra R K] (ϖ : R) [IsLocalization.Away ϖ K]
    [CommRing B] [Algebra R B] [CommRing B'] [Algebra B B'] [Algebra K B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R K B'] [IsLocalization.Away (algebraMap R B ϖ) B']
    (d : ℕ) (β : Module.Basis (Fin d) B (Ω[B⁄R]))
    (σ : ⋀[B']^d (Ω[B'⁄K])) (hσ : Submodule.span B' {σ} = ⊤)
    [CommRing O] [IsDomain O] [IsNoetherianRing O] [Algebra B O] [Algebra R O] [IsScalarTower R B O]
    (M : Submonoid B) [IsLocalization M O]
    (hϖ0 : algebraMap R O ϖ ≠ 0) (hϖ : (Ideal.span {algebraMap R O ϖ}).IsPrime) :
    ∃ (b' : Module.Basis (Fin d) O (Ω[O⁄R])) (w : Oˣ) (m : ℤ),
      (∀ i, b' i = KaehlerDifferential.map R R B O (β i)) ∧
      ∀ (F : Type u) [Field F] [Algebra O F] [Algebra R F] [Algebra K F] [Algebra B F] [Algebra B' F]
        [IsScalarTower R O F] [IsScalarTower R K F] [IsScalarTower B O F] [IsScalarTower R B F]
        [IsScalarTower B B' F] [IsScalarTower K B' F],
        topFormMap K K B' F d σ =
          (algebraMap O F (w : O) * algebraMap O F (algebraMap R O ϖ) ^ m) •
            topFormMap R K O F d (exteriorPower.ιMulti O d b') := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_TopFormOrder_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
