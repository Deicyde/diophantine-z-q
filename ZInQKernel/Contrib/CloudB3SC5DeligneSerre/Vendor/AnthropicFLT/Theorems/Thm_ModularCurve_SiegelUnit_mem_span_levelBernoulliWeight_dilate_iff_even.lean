/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even (git blob 52dacaf19ff63ed49a205243773212d09b00910f, sha256 9758c7ab128e97860c13b75b78fddf3c77cea61001fe0c9a03f69167fbb28ec4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even (N : ℕ) [NeZero N]
    (φ : ZMod N → ℚ) :
    φ ∈ Submodule.span ℚ (Set.range fun s : ZMod N => fun r : ZMod N =>
        ((6 * (((s * r).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((s * r).val : ℕ) : ℤ) + (N : ℤ) ^ 2 : ℤ) : ℚ)) ↔
      ∀ r : ZMod N, φ (-r) = φ r := by
  revert N φ
  exact @_root_.P2MW.S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.solution
