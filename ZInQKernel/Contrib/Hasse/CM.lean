import ZInQKernel.Contrib.Hasse.Quartic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The CM character-sum calculation

The square-map pushforward includes the zero fiber. For `d ≠ 0`, multiplication
by `d` is the change of variable that accounts for the congruent-number twist.
-/

namespace ZInQ.Contrib.Hasse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The quadratic character is unchanged by inversion as a character. -/
theorem eta_inv : (eta F)⁻¹ = eta F :=
  ((quadraticChar_isQuadratic F).comp _).inv

/-- The square-map fiber formula, with the zero fiber included. -/
theorem sum_comp_sq (hF : ringChar F ≠ 2) (f : F → ℂ) :
    ∑ x : F, f (x ^ 2) = ∑ t : F, (eta F t + 1) * f t := by
  rw [← Fintype.sum_fiberwise (fun x : F => x ^ 2)]
  apply Finset.sum_congr rfl
  intro t _
  have hc : (Fintype.card {x : F // x ^ 2 = t} : ℂ) = eta F t + 1 := by
    have h := quadraticChar_card_sqrts hF t
    have h' : (Fintype.card {x : F // x ^ 2 = t} : ℤ) = quadraticChar F t + 1 := by
      simpa only [Set.toFinset_ofPred, Fintype.card_subtype] using h
    simp only [eta_apply]
    exact_mod_cast h'
  simp only [show ∀ x : {x : F // x ^ 2 = t}, f (x.val ^ 2) = f t from fun x => congrArg f x.prop,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]

/-- The cubic sum at `d = 1` is the sum of two quartic Jacobi sums.
The sign `eta (-1)` is retained explicitly, rather than silently normalized. -/
theorem cubic_sum_eq_jacobi (hF : ringChar F ≠ 2) {χ : MulChar F ℂ}
    (hχ4 : χ ^ 4 = 1) (hχ2 : χ ^ 2 = eta F) :
    ∑ x : F, eta F (x ^ 3 - x) =
      eta F (-1) * (jacobiSum χ (eta F) + jacobiSum χ⁻¹ (eta F)) := by
  have hχ3 : χ ^ 3 = χ⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hχ4]
  have hsquare (x : F) : eta F x = χ (x ^ 2) := by
    rw [map_pow, ← MulChar.pow_apply' _ (by norm_num), hχ2]
  calc
    _ = ∑ x : F, χ (x ^ 2) * eta F (x ^ 2 - 1) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [show x ^ 3 - x = x * (x ^ 2 - 1) by ring, map_mul, hsquare]
    _ = ∑ t : F, (eta F t + 1) * (χ t * eta F (t - 1)) := sum_comp_sq hF (fun t => χ t * eta F (t - 1))
    _ = ∑ t : F, (χ t + χ⁻¹ t) * (eta F (-1) * eta F (1 - t)) := by
      apply Finset.sum_congr rfl
      intro t _
      have hp : eta F t * χ t = χ⁻¹ t := by
        rw [← hχ2, MulChar.pow_apply' _ (by norm_num), ← pow_succ, ← MulChar.pow_apply' _ (by norm_num), hχ3]
      rw [show t - 1 = (-1) * (1 - t) by ring, map_mul]
      linear_combination hp * (eta F (-1) * eta F (1 - t))
    _ = _ := by
      simp only [jacobiSum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      ring

/-- The exact quadratic-twist normalization for every nonzero `d`. -/
theorem cubic_sum_twist (d : F) (hd : d ≠ 0) :
    ∑ x : F, eta F (x ^ 3 - d ^ 2 * x) =
      eta F d * ∑ x : F, eta F (x ^ 3 - x) := by
  rw [← Fintype.sum_bijective _ (mulLeft_bijective₀ d hd)
    (fun x => eta F ((d * x) ^ 3 - d ^ 2 * (d * x)))
    (fun x => eta F (x ^ 3 - d ^ 2 * x)) (fun _ => rfl), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  change eta F ((d * x) ^ 3 - d ^ 2 * (d * x)) = eta F d * eta F (x ^ 3 - x)
  rw [show (d * x) ^ 3 - d ^ 2 * (d * x) = d ^ 3 * (x ^ 3 - x) by ring, map_mul, map_pow]
  have hs : eta F d ^ 2 = 1 := by
    simp only [eta_apply]
    exact_mod_cast quadraticChar_sq_one hd
  rw [pow_succ, hs, one_mul]

/-- The cubic quadratic-character sum satisfies Hasse's bound at split primes,
using a constructed quartic character rather than a bound hypothesis. -/
theorem norm_cubic_sum_le (hF : ringChar F ≠ 2) (h4 : 4 ∣ Fintype.card F - 1)
    (d : F) (hd : d ≠ 0) :
    ‖∑ x : F, eta F (x ^ 3 - d ^ 2 * x)‖ ≤ 2 * Real.sqrt (Fintype.card F) := by
  obtain ⟨χ, hχ, hχ2⟩ := exists_quartic hF h4
  have hχ1 : χ ≠ 1 := by
    intro h; simp [h] at hχ
  have hχ4 : χ ^ 4 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hη1 : eta F ≠ 1 := by
    rw [← hχ2]
    apply pow_ne_one_of_lt_orderOf (by norm_num)
    rw [hχ]; norm_num
  have hχφ : χ * eta F ≠ 1 := by
    rw [← hχ2, ← pow_succ']
    apply pow_ne_one_of_lt_orderOf (by norm_num)
    rw [hχ]; norm_num
  have hχiφ : χ⁻¹ * eta F ≠ 1 := by
    simpa [← hχ2, pow_two, ← mul_assoc] using hχ1
  have hn1 := norm_jacobiSum hχ1 hη1 hχφ
  have hn2 := norm_jacobiSum (inv_ne_one.mpr hχ1) hη1 hχiφ
  have hd1 : ‖eta F d‖ = 1 := by
    rcases quadraticChar_dichotomy hd with h | h <;> simp [h]
  have hm1 : ‖eta F (-1)‖ = 1 := by
    rcases quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)) with h | h <;> simp [h]
  rw [cubic_sum_twist d hd, norm_mul, hd1, one_mul,
    cubic_sum_eq_jacobi hF hχ4 hχ2, norm_mul, hm1, one_mul]
  calc
    _ ≤ ‖jacobiSum χ (eta F)‖ + ‖jacobiSum χ⁻¹ (eta F)‖ := norm_add_le _ _
    _ = 2 * Real.sqrt (Fintype.card F) := by rw [hn1, hn2]; ring

end ZInQ.Contrib.Hasse
