import ZInQKernel.RouteK.Rank.LFunctionCd
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# P1: `a_p(C_d) = 0` for `p ≡ 3 (mod 4)`

For odd squarefree `d` and a prime `p ∤ 2d`, `LFunction_cd_apply_prime_eq_sub_card`
(`RouteK/Rank/LFunctionCd.lean`) gives the Dirichlet coefficient of Mathlib's `L(C_d, s)` at `p` as
`p − #{(x, y) ∈ 𝔽_p² : y² = x³ − d² x}`. Counting the square roots with the quadratic character `χ`
of `𝔽_p` (`quadraticChar_card_sqrts`) turns this into the character sum

  `a_p(C_d) = − Σ_{x ∈ 𝔽_p} χ(x³ − d² x)`        (`LFunction_cd_apply_prime_eq_neg_charSum`).

The polynomial `x³ − d² x` is odd, so the substitution `x ↦ −x` multiplies the sum by `χ(−1)`;
for `p ≡ 3 (mod 4)`, `χ(−1) = −1` and the sum vanishes:

* `LFunction_cd_apply_prime_of_mod_four_eq_three`: `a_p(C_d) = 0`;
* `natCard_point_cd_of_mod_four_eq_three`: `#C_d(𝔽_p) = p + 1` (point at infinity included).

The generic counting lemma `card_solutions_eq` (`#{y² = g(x)} = q + Σ_x χ(g x)` over any finite
field of odd characteristic) is reused by the Hasse bound (`Hasse.lean`).
-/

namespace ZInQ.Contrib.PSide

open ZInQ.Literature WeierstrassCurve

section Generic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Points of `y² = g(x)` by the quadratic character**: over a finite field of odd
characteristic, `#{(x, y) : y² = g x} = #F + Σ_x χ(g x)`. -/
theorem card_solutions_eq (hF : ringChar F ≠ 2) (g : F → F) :
    (Nat.card {xy : F × F // xy.2 ^ 2 = g xy.1} : ℤ) =
      Fintype.card F + ∑ x, quadraticChar F (g x) := by
  classical
  have h1 : ∀ x : F, ((Finset.univ.filter fun y : F => y ^ 2 = g x).card : ℤ) =
      quadraticChar F (g x) + 1 := by
    intro x
    rw [← quadraticChar_card_sqrts hF (g x)]
    congr 2
    ext y; simp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  simp_rw [Finset.sum_boole, h1, Finset.sum_add_distrib]
  simp [add_comm]

/-- The character sum of an odd function vanishes when `−1` is not a square. -/
theorem charSum_odd_eq_zero (hneg : quadraticChar F (-1) = -1)
    (g : F → F) (hg : ∀ x, g (-x) = -g x) : ∑ x, quadraticChar F (g x) = 0 := by
  have h : ∑ x, quadraticChar F (g x) = ∑ x, quadraticChar F (g (-x)) :=
    (Fintype.sum_equiv (Equiv.neg F) _ _ (fun x => rfl)).symm
  simp_rw [hg, neg_eq_neg_one_mul (g _), map_mul, hneg, neg_one_mul, Finset.sum_neg_distrib] at h
  linarith

end Generic

section Cd

/-- `ringChar (ZMod p) ≠ 2` for an odd prime `p`. -/
theorem ringChar_zmod_ne_two {p : ℕ} (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp2

theorem ne_two_of_not_dvd {p d : ℕ} (hp : ¬ p ∣ 2 * d) : p ≠ 2 := by
  rintro rfl; exact hp (dvd_mul_right 2 d)

/-- **`a_p(C_d)` as a character sum**: for odd squarefree `d` and a prime `p ∤ 2d`,
`a_p(C_d) = − Σ_{x ∈ 𝔽_p} χ(x³ − d² x)`, `χ` the quadratic character of `𝔽_p`. -/
theorem LFunction_cd_apply_prime_eq_neg_charSum {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 2 * d) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p =
      -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (d : ZMod p) ^ 2 * x) := by
  rw [LFunction_cd_apply_prime_eq_sub_card hd hsq p hp,
    card_solutions_eq (ringChar_zmod_ne_two (ne_two_of_not_dvd hp))
      (fun x : ZMod p => x ^ 3 - (d : ZMod p) ^ 2 * x), ZMod.card]
  ring

/-- `χ(−1) = −1` in `𝔽_p` for `p ≡ 3 (mod 4)`. -/
theorem quadraticChar_zmod_neg_one_of_mod_four {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = -1 := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp4
  rw [quadraticChar_neg_one (ringChar_zmod_ne_two hp2), ZMod.card]
  exact ZMod.χ₄_nat_three_mod_four hp4

/-- **P1: `a_p(C_d) = 0` for `p ≡ 3 (mod 4)`**: for odd squarefree `d` and a prime
`p ≡ 3 (mod 4)` with `p ∤ 2d`, the Dirichlet coefficient of Mathlib's `L(C_d, s)` at `p` is `0`. -/
theorem LFunction_cd_apply_prime_of_mod_four_eq_three {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) (hp : ¬ p ∣ 2 * d) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p = 0 := by
  rw [LFunction_cd_apply_prime_eq_neg_charSum hd hsq p hp,
    charSum_odd_eq_zero (quadraticChar_zmod_neg_one_of_mod_four hp4) _ (fun x => by ring),
    neg_zero]

/-- **P1, point-count form**: `#C_d(𝔽_p) = p + 1` (point at infinity included) for a prime
`p ≡ 3 (mod 4)` with `p ∤ 2d`. (No hypothesis on `d` is needed here.) -/
theorem natCard_point_cd_of_mod_four_eq_three {d : ℕ} (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3)
    (hp : ¬ p ∣ 2 * d) :
    Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point = p + 1 := by
  rw [natCard_point_shortCurve_zmod p hp]
  congr 1
  have h := card_solutions_eq (ringChar_zmod_ne_two (ne_two_of_not_dvd hp))
    (fun x : ZMod p => x ^ 3 - (d : ZMod p) ^ 2 * x)
  rw [charSum_odd_eq_zero (quadraticChar_zmod_neg_one_of_mod_four hp4) _ (fun x => by ring),
    ZMod.card,
    add_zero] at h
  exact_mod_cast h

/-- P1 for the odd squarefree `d` of the CR₃ Props, stated with `p ∤ d` (for `p ≡ 3 (mod 4)`,
`p ∤ 2d ↔ p ∤ d`). -/
theorem LFunction_cd_apply_prime_of_mod_four_eq_three' {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (p : ℕ) [hp' : Fact p.Prime] (hp4 : p % 4 = 3) (hp : ¬ p ∣ d) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p = 0 := by
  refine LFunction_cd_apply_prime_of_mod_four_eq_three hd hsq p hp4 fun h => ?_
  rcases (Nat.Prime.dvd_mul hp'.out).mp h with h2 | h2
  · have := Nat.le_of_dvd (by norm_num) h2; interval_cases p <;> simp_all
  · exact hp h2

end Cd

end ZInQ.Contrib.PSide
