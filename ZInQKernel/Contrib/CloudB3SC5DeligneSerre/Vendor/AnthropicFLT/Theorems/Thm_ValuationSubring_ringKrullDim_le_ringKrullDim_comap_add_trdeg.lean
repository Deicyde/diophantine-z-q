/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg (git blob 8d301a57e6f21462170d9867e14c9a7bc08c2574, sha256 19a9f99cb446e4b6e61297ad3da0e1f0582ba0e89d3f3bd3b8e0ba120bd4aa5e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) :
    ringKrullDim A ≤ ringKrullDim (A.comap (algebraMap K L)) +
      (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) := by
  revert K L A
  exact @_root_.P2MW.S_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg.solution
