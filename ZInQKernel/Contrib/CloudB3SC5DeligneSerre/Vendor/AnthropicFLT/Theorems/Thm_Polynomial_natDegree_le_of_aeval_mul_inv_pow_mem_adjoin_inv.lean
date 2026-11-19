/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv (git blob efcd7515d6021689c9ade234cea5ebc3a84abb1d, sha256 a1a23b4da7b80b509a39e2556673a7e1579733b16500d44dd1335f5a57f4af4d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Polynomial.natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (c : Polynomial L) (n : ℕ)
    (h : Polynomial.aeval x c * (x ^ n)⁻¹ ∈ Algebra.adjoin L ({x⁻¹} : Set F)) :
    c.natDegree ≤ n := by
  revert L F x hxL hx0 c n h
  exact @_root_.P2MW.S_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv.solution
