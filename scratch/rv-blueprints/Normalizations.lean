import Mathlib

/-!
# rv-blueprints: the normalization arithmetic behind leaves R21 and R22 (bp-faltings §1)

`h_D = h_F + (g/2) log π` (Deligne's metric `(i/2π)^g` versus Faltings' `(i/2)^g`).

* `bost_F_of_D`: a Deligne-normalized Bost bound `h_D ≥ −(g/2) log(2π)` gives the form used by
  leaf R21, `h_F ≥ −(3/2) g`, because `log(2π²) < 3`.
* `log_pi_lt_three`: the shift `log π` (`g = 2`) is below the `+3` of the hardened R22.
* `faltings_le_deligne`: `h_F ≤ h_D`, so an upper bound on `h_D` (R18 if Javanpeykar's height
  were Deligne-normalized) gives the same upper bound on `h_F`, and conversely a bound stated
  with `max(h_D, …)` on the right (R19 if Gaudron–Rémond were Deligne-normalized) does **not**
  give the bound with `max(h_F, …)`: `faltings_kappa_le` shows the `h_F` form is the smaller
  (stronger) right side.
-/

namespace RvBlueprints

open Real

theorem log_two_pi_sq_lt_three : Real.log (2 * π ^ 2) < 3 := by
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < π := Real.pi_pos
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h1 : 2 * π ^ 2 < 19.85 := by nlinarith
  have h2 : (19.85 : ℝ) < Real.exp 3 := by
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h0 : (0 : ℝ) ≤ 2.7182818283 := by norm_num
    calc (19.85 : ℝ) < 2.7182818283 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := by gcongr
  have hpos : 0 < 2 * π ^ 2 := by positivity
  rw [Real.log_lt_iff_lt_exp hpos]
  linarith

/-- R21 from a Deligne-normalized Bost bound. -/
theorem bost_F_of_D (g : ℕ) (hF hD : ℝ) (hrel : hD = hF + (g / 2 : ℝ) * Real.log π)
    (hB : -((g / 2 : ℝ) * Real.log (2 * π)) ≤ hD) : -(3 / 2 : ℝ) * g ≤ hF := by
  have hlog : Real.log (2 * π) + Real.log π = Real.log (2 * π ^ 2) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; ring_nf
  have hg : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have h3 := log_two_pi_sq_lt_three
  have : (g / 2 : ℝ) * Real.log (2 * π ^ 2) ≤ (g / 2 : ℝ) * 3 :=
    mul_le_mul_of_nonneg_left h3.le (by positivity)
  nlinarith

theorem log_pi_lt_three : Real.log π < 3 := by
  have hpi : π < 3.15 := Real.pi_lt_d2
  have h3 : Real.log π < Real.log (2 * π ^ 2) := by
    apply Real.log_lt_log Real.pi_pos
    nlinarith [Real.pi_gt_three]
  linarith [log_two_pi_sq_lt_three]

theorem faltings_le_deligne (g : ℕ) (hF : ℝ) : hF ≤ hF + (g / 2 : ℝ) * Real.log π := by
  have : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hg : (0 : ℝ) ≤ g / 2 := by positivity
  nlinarith

/-- Gaudron–Rémond's `κ` is monotone in the height: the `h_F` form of the bound is at most the
`h_D` form, so it is the stronger statement. -/
theorem faltings_kappa_le (g : ℕ) (d hF : ℝ) :
    max (max hF (Real.log d)) 1 ≤ max (max (hF + (g / 2 : ℝ) * Real.log π) (Real.log d)) 1 := by
  have := faltings_le_deligne g hF
  exact max_le_max (max_le_max this le_rfl) le_rfl

end RvBlueprints

#print axioms RvBlueprints.bost_F_of_D
#print axioms RvBlueprints.log_pi_lt_three
#print axioms RvBlueprints.faltings_kappa_le
