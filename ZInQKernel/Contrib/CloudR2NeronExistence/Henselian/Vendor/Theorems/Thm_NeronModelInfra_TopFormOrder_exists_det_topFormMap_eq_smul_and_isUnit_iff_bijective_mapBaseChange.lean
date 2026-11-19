import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_TopFormOrder_exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange.lean
Original Git blob: 404df71189fb13f279c60f26ec0072d3df9e2498
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_TopFormOrder_exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open TensorProduct NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange
    (R' K' O' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O'] [Algebra R' O'] [CommRing O] [Algebra R' O] [Algebra O' O] [IsScalarTower R' O' O]
    [CommRing F] [Algebra O F] [Algebra O' F] [IsScalarTower O' O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    (d : ℕ) (b' : Module.Basis (Fin d) O' (Ω[O'⁄R'])) (b : Module.Basis (Fin d) O (Ω[O⁄R'])) :
    ∃ h : O,
      (letI := moduleAlong O' F (⋀[F]^d (Ω[F⁄K']))
       letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
       topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b') =
         algebraMap O F h • topFormMap R' K' O F d (exteriorPower.ιMulti O d b)) ∧
      (IsUnit h ↔ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_TopFormOrder_exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
