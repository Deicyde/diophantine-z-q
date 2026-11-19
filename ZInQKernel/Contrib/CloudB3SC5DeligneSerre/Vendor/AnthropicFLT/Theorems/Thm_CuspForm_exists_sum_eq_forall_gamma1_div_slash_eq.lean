/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq (git blob 0b2c419bb8ef9c5e5de20a45ac52e27cadc3cdef, sha256 b38563d002da5cac7c64fd6faa0ab236c1b0ea4d678ab9a8c50ee87d0e89161e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem CuspForm.exists_sum_eq_forall_gamma1_div_slash_eq
    (N : ℕ) [NeZero N] (k : ℤ) (F : ℕ → CuspForm (Gamma N) k)
    (hF : ∀ p ∈ N.primeFactors,
      (⇑(F p) : UpperHalfPlane → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((N / p : ℕ) : ℤ) * ModularGroup.S⁻¹) = ⇑(F p))
    (hsum : ∀ γ ∈ Gamma1 N,
      (⇑(∑ p ∈ N.primeFactors, F p) : UpperHalfPlane → ℂ) ∣[k] γ =
        ⇑(∑ p ∈ N.primeFactors, F p)) :
    ∃ G : ℕ → CuspForm (Gamma N) k,
      (∀ p ∈ N.primeFactors, ∀ γ ∈ Gamma1 (N / p),
        (⇑(G p) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(G p)) ∧
      ∑ p ∈ N.primeFactors, G p = ∑ p ∈ N.primeFactors, F p := by
  revert N k F hF hsum
  exact @_root_.P2MW.S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq.solution
