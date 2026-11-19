/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal (git blob 7951de2fb6062d19fb57cdb17b8d85d2d4955c39, sha256 d68c0266d95147742f1729f5ea70c0b0f91452668c7bd49ec3c5faee2a3c9121).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace

open scoped Classical in

theorem NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal
    (K : Type) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    SignType.sign (Algebra.norm ℚ x) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) := by
  revert K x hx
  exact @_root_.P2MW.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.solution
