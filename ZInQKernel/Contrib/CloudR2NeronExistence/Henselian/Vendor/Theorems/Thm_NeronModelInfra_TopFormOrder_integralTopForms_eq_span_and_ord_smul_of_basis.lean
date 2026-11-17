import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis.lean
Original Git blob: ed337e50c3374fed1d72d7d6af0dcf6ad33aed91
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis

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

theorem NeronModelInfra.TopFormOrder.integralTopForms_eq_span_and_ord_smul_of_basis
    (R' K' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F]
    (d : ℕ) (b : Module.Basis (Fin d) O (Ω[O⁄R'])) :
    letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
    integralTopForms R' K' O F d =
        Submodule.span O {topFormMap R' K' O F d (exteriorPower.ιMulti O d b)} ∧
      ∀ a : F, a ≠ 0 → topFormMap R' K' O F d (exteriorPower.ιMulti O d b) ≠ 0 →
        ord R' K' O d F (a • topFormMap R' K' O F d (exteriorPower.ιMulti O d b)) = addOrd O F a := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
