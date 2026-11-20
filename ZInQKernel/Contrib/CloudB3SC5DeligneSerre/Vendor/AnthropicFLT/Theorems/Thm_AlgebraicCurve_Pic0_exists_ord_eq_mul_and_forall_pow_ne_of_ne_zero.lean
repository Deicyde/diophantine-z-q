/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero (git blob a8cfaeede0bd1c861865496ce63c8c11a51df33d, sha256 de50f2520139a0d8d2ca4bc6af65ec94ea85a5d9a849e515c97f729d557b1f86).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (hn : n ≠ 0) {x : Pic0 K F}
    (hx : x ∈ Pic0.torsion K F n) (hx0 : x ≠ 0) :
    ∃ (D : Divisor.degZero (K := K) (F := F)) (f : F),
      Pic0.mk D = x ∧ f ≠ 0 ∧ (∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) ∧
        ∀ b : F, b ^ n ≠ f := by
  revert K F n hn x hx hx0
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero.solution
