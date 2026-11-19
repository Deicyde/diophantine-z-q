/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Int_exists_modEq_and_modEq_and_isCoprime (git blob 418410f73275fd8b4b65a4dba9a3a35bebab2959, sha256 d49221cfec6985be246fbf9c106dc0a6b9d402d4d781228afd095dd584eb3370).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Int_exists_modEq_and_modEq_and_isCoprime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Int.exists_modEq_and_modEq_and_isCoprime {n c d : ℤ}
    (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) :
    ∃ c' d' : ℤ, c' ≡ c [ZMOD n] ∧ d' ≡ d [ZMOD n] ∧ IsCoprime c' d' := by
  revert n c d h
  exact @_root_.P2MW.S_Int_exists_modEq_and_modEq_and_isCoprime.solution
