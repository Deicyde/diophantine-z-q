import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits.lean
Original Git blob: 7e648271aeff6fa41d91d00f71d4d7d7a96964d6
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

theorem ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
    {K : Type*} [Field K] {ι : Type*} [Finite ι] (R : ι → ValuationSubring K)
    (hR : ∀ i j, R i ≤ R j → i = j) (a : ι → K) (ha : ∀ i, a i ∈ R i) :
    ∃ z : K, ∀ i, z ∈ R i ∧ z - a i ∈ (R i).nonunits := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
