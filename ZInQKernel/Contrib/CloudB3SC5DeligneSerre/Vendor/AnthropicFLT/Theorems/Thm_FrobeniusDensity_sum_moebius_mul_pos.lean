/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_sum_moebius_mul_pos (git blob 439134313fd888a5ff0932e455d57f0c3834b2f7, sha256 5ebbcae74e0735334e49d3313fadb8a3caa45bf76c60c14085a394ea86fc4684).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.GroupTheory.OrderOfElement
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_sum_moebius_mul_pos

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Classical in
theorem FrobeniusDensity.sum_moebius_mul_pos {G : Type*} [Group G] [Finite G] (σ : G) :
    0 < ∑ f ∈ (orderOf σ).divisors,
      (ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) := by
  revert G σ
  exact @_root_.P2MW.S_FrobeniusDensity_sum_moebius_mul_pos.solution
