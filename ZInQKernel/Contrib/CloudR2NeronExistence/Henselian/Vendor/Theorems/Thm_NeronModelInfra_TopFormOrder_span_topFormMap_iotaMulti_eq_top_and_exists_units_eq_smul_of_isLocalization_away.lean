import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_TopFormOrder_span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away.lean
Original Git blob: bde0a10b23308d6ba48eb63f0d7d3ab84e44feda
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_TopFormOrder_span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away

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

theorem NeronModelInfra.TopFormOrder.span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away
    (R K B B' : Type u) [CommRing R] [CommRing K] [Algebra R K] (ϖ : R) [IsLocalization.Away ϖ K]
    [CommRing B] [Algebra R B] [CommRing B'] [Algebra B B'] [Algebra K B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R K B'] [IsLocalization.Away (algebraMap R B ϖ) B']
    (d : ℕ) (β : Module.Basis (Fin d) B (Ω[B⁄R])) :
    letI := moduleAlong B B' (⋀[B']^d (Ω[B'⁄K]))
    Submodule.span B' {topFormMap R K B B' d (exteriorPower.ιMulti B d β)} = ⊤ ∧
      ∀ σ : ⋀[B']^d (Ω[B'⁄K]), Submodule.span B' {σ} = ⊤ →
        ∃ u : B'ˣ, σ = (u : B') • topFormMap R K B B' d (exteriorPower.ιMulti B d β) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_TopFormOrder_span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
