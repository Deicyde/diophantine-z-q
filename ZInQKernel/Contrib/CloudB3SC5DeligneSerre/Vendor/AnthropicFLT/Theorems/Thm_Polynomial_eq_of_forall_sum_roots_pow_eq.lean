/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Polynomial_eq_of_forall_sum_roots_pow_eq (git blob b0ddaa389df4ba03905725df0ee0be3b1bba3c3d, sha256 ddeb2d72e5ab6f257a4a4c9bc243a099db0f8f9842df65f3da5481a9c475dc52).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Polynomial_eq_of_forall_sum_roots_pow_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Polynomial.eq_of_forall_sum_roots_pow_eq {K : Type*} [Field K] [CharZero K]
    (P Q : Polynomial K) (hP : P.Monic) (hQ : Q.Monic) (hPs : P.Splits) (hQs : Q.Splits)
    (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ n : ℕ, 0 < n →
      (P.roots.map (fun z => z ^ n)).sum = (Q.roots.map (fun z => z ^ n)).sum) :
    P = Q := by
  revert K P Q hP hQ hPs hQs hdeg h
  exact @_root_.P2MW.S_Polynomial_eq_of_forall_sum_roots_pow_eq.solution
