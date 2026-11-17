/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits (git blob 7e648271aeff6fa41d91d00f71d4d7d7a96964d6, sha256 12e5854b60ba76dd9eadafefc32c0e5ca2bd0106d268ab44fcaf3cc160e4ea55).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
    {K : Type*} [Field K] {ι : Type*} [Finite ι] (R : ι → ValuationSubring K)
    (hR : ∀ i j, R i ≤ R j → i = j) (a : ι → K) (ha : ∀ i, a i ∈ R i) :
    ∃ z : K, ∀ i, z ∈ R i ∧ z - a i ∈ (R i).nonunits := by
  revert K ι R hR a ha
  exact @_root_.P2MW.S_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits.solution
