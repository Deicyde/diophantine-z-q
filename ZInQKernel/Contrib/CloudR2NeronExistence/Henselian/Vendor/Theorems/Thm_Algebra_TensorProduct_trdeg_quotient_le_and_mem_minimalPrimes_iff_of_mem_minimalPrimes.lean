import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_Algebra_TensorProduct_trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes.lean
Original Git blob: ec886858607c514dbe7c7a0a23a9fac114f17966
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_Algebra_TensorProduct_trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes

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

theorem Algebra.TensorProduct.trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes
    {R A A' : Type u} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    [Algebra.FiniteType R A']
    (𝔓 : Ideal (A ⊗[R] A')) [𝔓.IsPrime]
    (h : 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom ∈
      ((𝔓.under R).map (algebraMap R A')).minimalPrimes) :
    Algebra.trdeg (A ⧸ 𝔓.under A) ((A ⊗[R] A') ⧸ 𝔓) ≤
        Algebra.trdeg
          (R ⧸ (𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom).under R)
          (A' ⧸ 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom) ∧
      (𝔓 ∈ ((𝔓.under A).map (algebraMap A (A ⊗[R] A'))).minimalPrimes ↔
        Algebra.trdeg (A ⧸ 𝔓.under A) ((A ⊗[R] A') ⧸ 𝔓) =
          Algebra.trdeg
            (R ⧸ (𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom).under R)
            (A' ⧸ 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_Algebra_TensorProduct_trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
