import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_TopFormOrder_le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul.lean
Original Git blob: ad112e5b3ea648a5800a6288e5a596d3d2a1544a
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_TopFormOrder_le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul

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

theorem NeronModelInfra.TopFormOrder.le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
    (R' K' O' O F : Type u)
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    (ϖ : R') (hϖ : IsLocalRing.maximalIdeal R' = Ideal.span {ϖ})
    [CommRing O'] [IsDomain O'] [Algebra R' O']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Algebra O' O] [IsScalarTower R' O' O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra O' F] [IsScalarTower O' O F] [IsFractionRing O' F]
    [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    (d : ℕ) (b' : Module.Basis (Fin d) O' (Ω[O'⁄R'])) (b : Module.Basis (Fin d) O (Ω[O⁄R']))
    (m : ℤ) (u : O'ˣ) (σ : ⋀[F]^d (Ω[F⁄K']))
    (hσ : letI := moduleAlong O' F (⋀[F]^d (Ω[F⁄K']))
      σ = (algebraMap O' F (u : O') * algebraMap O' F (algebraMap R' O' ϖ) ^ m) •
        topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b')) :
    m ≤ ord R' K' O d F σ ∧
    (ord R' K' O d F σ = m ↔ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_TopFormOrder_le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
