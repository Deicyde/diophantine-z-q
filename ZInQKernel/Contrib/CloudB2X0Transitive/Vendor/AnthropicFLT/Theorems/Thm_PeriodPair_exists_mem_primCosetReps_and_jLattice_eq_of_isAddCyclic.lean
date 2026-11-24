/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PrimCosetReps
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
theorem PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic
    {N : ℕ} [NeZero N] (L L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice) (hidx : PeriodPair.sublatticeIndex L L' = N)
    (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
    ∃ (a b d : ℕ) (τ σ : ℍ), (a, b, d) ∈ ModularCurve.primCosetReps N ∧
      (σ : ℂ) = ((a : ℂ) * τ + b) / d ∧
      L.jLattice = (PeriodPair.ofTau τ).jLattice ∧ L'.jLattice = (PeriodPair.ofTau σ).jLattice := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic.solution
