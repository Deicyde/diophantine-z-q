import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_TopFormOrder_topFormMap_topFormMap.lean
Original Git blob: 6cf01e6bd6cd02178fe20f8646d721d9ed9dc8b8
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_TopFormOrder_topFormMap_topFormMap

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

open NeronModelInfra.TopFormOrder

universe u

theorem NeronModelInfra.TopFormOrder.topFormMap_topFormMap
    (R₁ R₂ R₃ O₁ O₂ O₃ : Type u) [CommRing R₁] [CommRing R₂] [CommRing R₃]
    [CommRing O₁] [CommRing O₂] [CommRing O₃]
    [Algebra R₁ R₂] [Algebra R₂ R₃] [Algebra R₁ R₃] [IsScalarTower R₁ R₂ R₃]
    [Algebra R₁ O₁] [Algebra R₂ O₂] [Algebra R₃ O₃]
    [Algebra O₁ O₂] [Algebra O₂ O₃] [Algebra O₁ O₃] [IsScalarTower O₁ O₂ O₃]
    [Algebra R₁ O₂] [IsScalarTower R₁ O₁ O₂] [IsScalarTower R₁ R₂ O₂]
    [Algebra R₂ O₃] [IsScalarTower R₂ O₂ O₃] [IsScalarTower R₂ R₃ O₃]
    [Algebra R₁ O₃] [IsScalarTower R₁ O₁ O₃] [IsScalarTower R₁ R₃ O₃]
    (d : ℕ) (η : ⋀[O₁]^d (Ω[O₁⁄R₁])) :
    topFormMap R₂ R₃ O₂ O₃ d (topFormMap R₁ R₂ O₁ O₂ d η) = topFormMap R₁ R₃ O₁ O₃ d η := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_TopFormOrder_topFormMap_topFormMap.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
