/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow (git blob 535b388306bb1fce00bb773b9de328fe799423c5, sha256 62b67eb5301b8bbead0b86705bf537009302038294041c61551a80fab2a2cf32).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.LSeries.Convergence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped ComplexOrder

theorem LSeries.exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow
    {ι : Type*} (N : ι → ℕ) (hN : ∀ i : ι, (N i).Prime) (hinj : Function.Injective N)
    (c : ι → ℕ → ℝ) (hc0 : ∀ i : ι, c i 0 = 0) (hc : ∀ (i : ι) (m : ℕ), 0 ≤ c i m)
    (B : ℝ) (hcB : ∀ (i : ι) (m : ℕ), c i m ≤ B * (N i : ℝ) ^ m) :
    ∃ d : ℕ → ℝ, (∀ n : ℕ, 0 ≤ d n) ∧
      (∀ (i : ι) (m : ℕ), 0 < m → d (N i ^ m) = c i m) ∧
      (∀ n : ℕ, d n ≠ 0 → ∃ (i : ι) (m : ℕ), 0 < m ∧ N i ^ m = n) ∧
      LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ ((2 : ℝ) : EReal) ∧
      (∀ s : ℂ, 2 < s.re →
        (∀ i : ι, Summable (fun m : ℕ => (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m)) ∧
        HasSum (fun i : ι => ∑' m : ℕ, (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m)
          (LSeries (fun n => (d n : ℂ)) s)) ∧
      ∀ σ : ℝ, LSeriesSummable (fun n => (d n : ℂ)) σ →
        Summable (fun i : ι => c i 1 * (N i : ℝ) ^ (-σ)) ∧
        ∑' i : ι, c i 1 * (N i : ℝ) ^ (-σ) ≤ (LSeries (fun n => (d n : ℂ)) σ).re := by
  revert ι N hN hinj c hc0 hc B hcB
  exact @_root_.P2MW.S_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow.solution
