import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq.lean
Original Git blob: 031b1af946e293a368331cc7c5b70d7ddeb21c77
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq

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

open TensorProduct

universe u

theorem Algebra.isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hqp : q ≤ p) [Algebra.IsSmoothAt R q]
    (h : Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) =
      Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R])) :
    Algebra.IsSmoothAt R p := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
