/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet (git blob 2388d2716d36b051ea1aa3d9a6869a9b8c545c97, sha256 6463fdb4a2aae04ce147427987a8ca0b13c9935c72709f7c73c5e767e319d6e6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem LanglandsTunnell.casimir_pos_or_discrete_or_zero_of_weightSet
    (lam : ℝ) (S : Set ℤ) (hS : S.Nonempty)
    (hminus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n - 2))
    (hplus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n + 2))
    (clminus : ∀ n ∈ S, 0 < 4 * lam + n * (n - 2) → n - 2 ∈ S)
    (clplus : ∀ n ∈ S, 0 < 4 * lam + n * (n + 2) → n + 2 ∈ S) :
    0 < lam ∨
      (∃ k₀ : ℕ, 2 ≤ k₀ ∧ lam = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
        ∀ n ∈ S, (k₀ : ℤ) ≤ |n| ∧ (n - k₀) % 2 = 0) ∨
      (lam = 0 ∧ (0 : ℤ) ∈ S) := by
  revert lam S hS hminus hplus clminus clplus
  exact @_root_.P2MW.S_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet.solution
