/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_dedekindPsi_mul_prime (git blob c9f80a5bb02c874f0b2ae191bfea2104fad50516, sha256 1a8eaa8fb16ab499c4a95599bdb94b3319116535b9a1405fa736b5989db04e63).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_dedekindPsi_prime
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_dedekindPsi_mul_prime

set_option autoImplicit false

open ModularCurve

theorem solution (M ℓ : ℕ) [NeZero M] (hℓ : ℓ.Prime) :
    dedekindPsi (M * ℓ) = (if ℓ ∣ M then ℓ else ℓ + 1) * dedekindPsi M := by
  have hM : M ≠ 0 := NeZero.ne M
  obtain ⟨k, M', hM', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM ℓ hℓ.ne_one
  have hcop : Nat.Coprime (ℓ ^ k) M' := (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hM'))
  have hcop' : Nat.Coprime M' ℓ := ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hM').symm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  ·
    simp only [pow_zero, one_mul] at hcop ⊢
    rw [if_neg hM', dedekindPsi_mul_of_coprime M' ℓ hcop', dedekindPsi_prime hℓ, mul_comm]
  ·
    have hdvd : ℓ ∣ ℓ ^ k * M' := dvd_mul_of_dvd_left (dvd_pow_self ℓ hk.ne') M'
    rw [if_pos hdvd]
    have e1 : ℓ ^ k * M' * ℓ = ℓ ^ (k + 1) * M' := by ring
    have hcop1 : Nat.Coprime (ℓ ^ (k + 1)) M' := Nat.Coprime.pow_left (k + 1) ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hM')
    rw [e1, dedekindPsi_mul_of_coprime _ _ hcop1, dedekindPsi_mul_of_coprime _ _ hcop,
      dedekindPsi_prime_pow ℓ (k + 1) hℓ (Nat.succ_ne_zero k), dedekindPsi_prime_pow ℓ k hℓ hk.ne', Nat.add_sub_cancel]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
    simp only [Nat.zero_add, Nat.add_sub_cancel]
    ring
