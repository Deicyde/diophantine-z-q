/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat (git blob 197ecdca4af0a98094cf0662b03595e2200899c5, sha256 3801f1a8de066835b4d17b2d8aa3752e184177b4bd508a81cc415e702b8c08cb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat

theorem solution
    {L : Type*} [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (A : ValuationSubring L) :
    Ring.KrullDimLE 1 A := by
  rw [Ring.krullDimLE_iff]
  have h := ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one A
  rw [trdeg_eq_zero, map_zero] at h
  simpa using h
