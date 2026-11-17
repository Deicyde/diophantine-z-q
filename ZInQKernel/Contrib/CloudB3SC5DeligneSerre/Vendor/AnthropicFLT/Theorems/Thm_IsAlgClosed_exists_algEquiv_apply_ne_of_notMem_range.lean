/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range (git blob 9d95056f432369f5354a7c258ae7631c91962680, sha256 68a2b26f76d98d461239ba5b1ff5524c7610bd8eae747e2dd8eee582ccf53042).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsAlgClosed E] [CharZero F] {c : E} (hc : c ∉ Set.range (algebraMap F E)) :
    ∃ σ : E ≃ₐ[F] E, σ c ≠ c := by
  revert F E c hc
  exact @_root_.P2MW.S_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range.solution
