/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv (git blob 4257d102ab63dde418436d5e1f53b900593524db, sha256 c328146bf6685bb80650db52feedd94b76083b6051d893ca226470c991df88d3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
theorem AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv {K : Type*} [Field K] {ι : Type*} [Finite ι]
    {v : ι → AbsoluteValue K ℝ} (hv : ∀ i, (v i).IsNontrivial) (hne : Pairwise fun i j => ¬(v i).IsEquiv (v j))
    (a : ι → K) {ε : ℝ} (hε : 0 < ε) : ∃ x : K, ∀ i, v i (x - a i) < ε := by
  revert K ι v hv hne a ε hε
  exact @_root_.P2MW.S_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv.solution
