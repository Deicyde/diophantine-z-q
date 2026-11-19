/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ArithmeticFunction_sum_moebius_filter_dvd (git blob 9b10b267602193e8a62dc78bea5bb0c9acf0782c, sha256 07ea813c3cd34f9077e334c3a5c5053188fc9286f52dc6ceca5acc8452bad4cc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ArithmeticFunction_sum_moebius_filter_dvd

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction Finset

theorem solution {n m : ℕ} (hn : n ≠ 0) (hm : m ∣ n) :
    ∑ f ∈ n.divisors, ArithmeticFunction.moebius (n / f) * (if m ∣ f then 1 else 0)
      = if m = n then 1 else 0 := by
  have hre : ∑ f ∈ n.divisors, μ (n / f) * (if m ∣ f then 1 else 0)
      = ∑ f ∈ n.divisors, μ f * (if m ∣ n / f then 1 else 0) := by
    rw [← Nat.sum_div_divisors n (fun f => μ f * (if m ∣ n / f then 1 else 0))]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [Nat.div_div_self (Nat.mem_divisors.mp hf).1 hn]
  rw [hre]
  have hsum : ∑ f ∈ n.divisors, μ f * (if m ∣ n / f then 1 else 0)
      = ∑ f ∈ (n / m).divisors, μ f := by
    rw [← Nat.divisors_filter_dvd_of_dvd hn (Nat.div_dvd_of_dvd hm), Finset.sum_filter]
    refine Finset.sum_congr rfl fun f hf => ?_
    have hfn : f ∣ n := (Nat.mem_divisors.mp hf).1
    have hiff : m ∣ n / f ↔ f ∣ n / m := by
      rw [Nat.dvd_div_iff_mul_dvd hfn, Nat.dvd_div_iff_mul_dvd hm, mul_comm]
    rw [if_congr hiff rfl rfl]
    split <;> simp
  rw [hsum]
  have hsum2 : ∑ d ∈ (n/m).divisors, μ d = if n/m = 1 then 1 else 0 := by
    have h2 : (μ * ζ : ArithmeticFunction ℤ) (n/m) = (1 : ArithmeticFunction ℤ) (n/m) := by
      rw [moebius_mul_coe_zeta]
    rwa [coe_mul_zeta_apply, one_apply] at h2
  rw [hsum2]
  congr 1
  simp only [eq_iff_iff]
  constructor
  · intro h; have := Nat.eq_mul_of_div_eq_right hm h; omega
  · rintro rfl; exact Nat.div_self (Nat.pos_of_ne_zero hn)
