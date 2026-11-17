import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular.lean
Original Git blob: 0364105d7dd8dadc5a2b5eb2d59449b9f4c03a9c
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular

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

universe u v

theorem AffineDilatation.nonempty_algHom_and_subsingleton_of_isSMulRegular
    {A : Type u} [CommRing A] (I : Ideal A) (a : A)
    {C : Type v} [CommRing C] [Algebra A C] (hreg : IsSMulRegular C a)
    (hI : I.map (algebraMap A C) ≤ Ideal.span {algebraMap A C a}) :
    Nonempty (AffineDilatation.Ring I a →ₐ[A] C) ∧
      Subsingleton (AffineDilatation.Ring I a →ₐ[A] C) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
