/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le (git blob c576c1982b8e754d1b88fa72f011034853c8cb6b, sha256 dc854093f3b657902bc1d5d6a6691765578bf34cde6434f41e64bb08c99d4b15).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem NumberField.Units.exists_forall_abs_sub_mult_mul_log_le (K : Type*) [Field K]
    [NumberField K] : ∃ R : ℝ, ∀ t : NumberField.InfinitePlace K → ℝ, ∑ w, t w = 0 →
      ∃ u : (NumberField.RingOfIntegers K)ˣ, ∀ w : NumberField.InfinitePlace K,
        |t w - (w.mult : ℝ) * Real.log (w (u : K))| ≤ R := by
  revert K
  exact @_root_.P2MW.S_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le.solution
