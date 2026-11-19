/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat (git blob 3db3d6f25bf27d3addd4e4484796f0db6ee21dc1, sha256 5500083ad38955ac767f0ba4469456e4541482377651b642c1d041ed896fb7ec).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.krullDimLE_one_of_isAlgebraic_rat
    {L : Type*} [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (A : ValuationSubring L) :
    Ring.KrullDimLE 1 A := by
  revert L A
  exact @_root_.P2MW.S_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat.solution
