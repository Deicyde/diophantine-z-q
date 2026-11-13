import ZInQKernel.Contrib.Hasse.CM
import ZInQKernel.RouteK.Rank.LFunctionCd

/-!
# The actual good-prime Hasse bound for `C_d`

The negation argument is adapted from the project's P1 PointCount proof at
`87c7160f457df93e58c4b564dfa04668576447d8`; it is used only in the inert case.
The split case uses the quartic character constructed in `Quartic.lean` and the
complete square-fiber and twist calculations in `CM.lean`.
-/

namespace ZInQ.Contrib.Hasse

open ZInQ.Literature WeierstrassCurve

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The affine count minus the field cardinality is exactly the character sum. -/
theorem affine_count_eq_char_sum (hF : ringChar F ≠ 2) (f : F → F) :
    (Nat.card {xy : F × F // xy.2 ^ 2 = f xy.1} : ℤ) =
      (Fintype.card F : ℤ) + ∑ x : F, quadraticChar F (f x) := by
  calc
    _ = ∑ x : F, (Fintype.card {y : F // y ^ 2 = f x} : ℤ) := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun x y : F => y ^ 2 = f x)),
        Fintype.card_sigma, Nat.cast_sum]
    _ = ∑ x : F, (quadraticChar F (f x) + 1) := by
      apply Finset.sum_congr rfl
      intro x _
      simpa only [Set.toFinset_ofPred, Fintype.card_subtype] using quadraticChar_card_sqrts hF (f x)
    _ = _ := by rw [Finset.sum_add_distrib]; simp; ring

/-- An odd function's quadratic-character sum vanishes in the inert case.
Adapted, with complex coefficients, from P1's negation-pairing proof. -/
theorem sum_eta_of_odd (f : F → F) (hf : ∀ x, f (-x) = -f x)
    (hminus : ¬ IsSquare (-1 : F)) : ∑ x : F, eta F (f x) = 0 := by
  have hχ : eta F (-1) = -1 := by
    simp only [eta_apply, quadraticChar_neg_one_iff_not_isSquare.mpr hminus, Int.cast_neg,
      Int.cast_one]
  have hodd (x : F) : eta F (f (-x)) = -eta F (f x) := by
    rw [hf x, neg_eq_neg_one_mul, map_mul, hχ, neg_one_mul]
  have hsum := Equiv.sum_comp (Equiv.neg F) (fun x => eta F (f x))
  simp only [Equiv.neg_apply, hodd, Finset.sum_neg_distrib] at hsum
  linear_combination -(1 / 2 : ℂ) * hsum

/-- The full finite-field cubic bound, including both congruence classes. -/
theorem norm_cubic_sum_le_all (hF : ringChar F ≠ 2) (d : F) (hd : d ≠ 0) :
    ‖∑ x : F, eta F (x ^ 3 - d ^ 2 * x)‖ ≤ 2 * Real.sqrt (Fintype.card F) := by
  by_cases h3 : Fintype.card F % 4 = 3
  · have hm : ¬ IsSquare (-1 : F) := by
      rw [FiniteField.isSquare_neg_one_iff, h3]; simp
    rw [sum_eta_of_odd (fun x : F => x ^ 3 - d ^ 2 * x) (fun x => by ring) hm, norm_zero]
    positivity
  · have hodd := FiniteField.odd_card_of_char_ne_two hF
    have h4 : 4 ∣ Fintype.card F - 1 := by omega
    exact norm_cubic_sum_le hF h4 d hd

end FiniteField

/-- Hasse for the exact affine equation used by the frozen downstream L-function. -/
theorem abs_affine_trace_le (p d : ℕ) [Fact p.Prime] (hpd : ¬ p ∣ 2 * d) :
    |(((p : ℤ) - Nat.card {xy : ZMod p × ZMod p //
      xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} : ℤ) : ℝ)|
      ≤ 2 * Real.sqrt p := by
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    rintro rfl
    exact hpd (dvd_mul_right 2 d)
  have hd : (d : ZMod p) ≠ 0 := by
    intro h
    exact hpd (((ZMod.natCast_eq_zero_iff d p).mp h).trans (dvd_mul_left d 2))
  have hcount := affine_count_eq_char_sum hF
    (fun x : ZMod p => x ^ 3 - (d : ZMod p) ^ 2 * x)
  have hsum : (((p : ℤ) - Nat.card {xy : ZMod p × ZMod p //
      xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} : ℤ) : ℂ) =
      -(∑ x : ZMod p, eta (ZMod p) (x ^ 3 - (d : ZMod p) ^ 2 * x)) := by
    simp only [eta_apply, ← Int.cast_sum]
    have hi : (p : ℤ) - Nat.card {xy : ZMod p × ZMod p //
        xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} =
        -(∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (d : ZMod p) ^ 2 * x)) := by
      simp only [ZMod.card] at hcount
      omega
    exact_mod_cast hi
  have h := norm_cubic_sum_le_all hF (d : ZMod p) hd
  rw [← norm_neg, ← hsum, Complex.norm_intCast, ZMod.card] at h
  exact h

/-- The actual Mathlib Dirichlet coefficient satisfies Hasse at every good prime.
No Hasse hypothesis is present. Oddness and squarefreeness are exactly the frozen
local-model identification's hypotheses, not inputs to the finite-field estimate. -/
theorem LFunction_cd_prime_hasse {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (p : ℕ) [Fact p.Prime] (hpd : ¬ p ∣ 2 * d) :
    |(((shortCurve (-(d : ℚ) ^ 2)).LFunction p : ℤ) : ℝ)| ≤ 2 * Real.sqrt p := by
  rw [LFunction_cd_apply_prime_eq_sub_card hd hsq p hpd]
  exact abs_affine_trace_le p d hpd

end ZInQ.Contrib.Hasse
