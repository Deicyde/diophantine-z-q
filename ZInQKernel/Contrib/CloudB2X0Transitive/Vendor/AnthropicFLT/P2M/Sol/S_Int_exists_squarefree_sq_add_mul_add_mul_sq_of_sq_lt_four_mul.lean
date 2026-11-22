/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_Nat_exists_squarefree_sq_add
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul

set_option autoImplicit false

theorem solution (t n : ℤ) (h : t ^ 2 < 4 * n) :
    ∃ a b : ℤ, b ≠ 0 ∧ Squarefree (a ^ 2 + t * a * b + n * b ^ 2).toNat ∧
      2 ≤ (a ^ 2 + t * a * b + n * b ^ 2).toNat := by
  set D : ℕ := (4 * n - t ^ 2).toNat with hD_def
  have hD1 : 1 ≤ D := by
    have : (1 : ℤ) ≤ 4 * n - t ^ 2 := by omega
    omega
  have hDcast : ((D : ℤ)) = 4 * n - t ^ 2 := by
    rw [hD_def]; exact Int.toNat_of_nonneg (by omega)
  obtain ⟨c, hc1, hsf⟩ := Nat.exists_squarefree_sq_add D hD1
  have hid : ((c : ℤ) - t) ^ 2 + t * ((c : ℤ) - t) * 2 + n * 2 ^ 2 = ((c ^ 2 + D : ℕ) : ℤ) := by
    push_cast [hDcast]; ring
  refine ⟨(c : ℤ) - t, 2, two_ne_zero, ?_, ?_⟩
  · rw [hid, Int.toNat_natCast]; exact hsf
  · rw [hid, Int.toNat_natCast]; nlinarith [sq_nonneg c]
