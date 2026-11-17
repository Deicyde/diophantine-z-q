/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_qExpansion_E6_eq_map_mk (git blob a2e33ac8bdbfc79e6308df3ff8db81af711ea682, sha256 69c304cd1fdb5717704a51b43b5940ee526ea7ef6681031c69a97078785104a9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.Bernoulli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_qExpansion_E6_eq_map_mk

open UpperHalfPlane ModularForm Finset

private lemma bernoulli'_five_s18 : bernoulli' 5 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

private lemma bernoulli'_six_s18 : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_five_s18, Nat.choose]

private lemma bernoulli_six_s18 : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six_s18]

theorem solution :
    UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆ =
      PowerSeries.map (Int.castRingHom ℂ)
        (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) := by
  ext m
  rw [show (ModularForm.E₆ : ModularForm _ 6) = E (by norm_num : 3 ≤ 6) from rfl]
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num : 3 ≤ 6) (by decide) m]
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs with hm
  · simp
  · have hB : (bernoulli 6 : ℂ) = 1 / 42 := by
      rw [bernoulli_six_s18]; push_cast; ring
    rw [ArithmeticFunction.sigma_apply]
    push_cast
    rw [hB]
    norm_num
