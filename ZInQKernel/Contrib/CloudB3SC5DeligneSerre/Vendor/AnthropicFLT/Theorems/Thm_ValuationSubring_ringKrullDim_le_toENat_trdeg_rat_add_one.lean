/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one (git blob d4af8959cd5011170497a9de026fc075f54cecdf, sha256 26c3823e6856fadf386c127729724e63ca58280618e1b8562bf1e4bd5c1b21b5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one
    {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) :
    ringKrullDim A ≤ (Cardinal.toENat (Algebra.trdeg ℚ L) : WithBot ℕ∞) + 1 := by
  revert L A
  exact @_root_.P2MW.S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one.solution
