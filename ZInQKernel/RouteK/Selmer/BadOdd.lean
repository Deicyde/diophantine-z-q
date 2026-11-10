import ZInQKernel.RouteK.Selmer.PadicSquare

/-!
# Odd primes dividing `d`

`docs/research/nt-prop0.md` §2.4, Lemma B: for an odd prime `p ∣ d` (`d` squarefree) the covering
`D_{a,b}` is soluble over `ℚ_p` iff `(a, b)` is one of the four torsion classes `(1, 1)`, `(d, 2)`,
`(−1, −d)`, `(−d, −2d)`, i.e. `a d^i (−1)^j` and `b 2^i (−d)^j` are squares for some
`i, j ∈ {0, 1}`.

The proof compares `‖x‖` with `‖d‖ = p⁻¹`. If `‖x‖ > ‖d‖` then `x ± d ≡ x` by (P), giving `(1, 1)`;
if `‖x‖ < ‖d‖` then `x ± d ≡ ±d`, giving `(−1, −d)`; if `‖x‖ = ‖d‖`, write `x = dt` with `t` a unit:
`t − 1` and `t + 1` are not both non-units (their difference is `2`), not both units (then
`‖x(x − d)(x + d)‖ = p⁻³` is not the norm of a square), and `p ∣ t ∓ 1` gives `(d, 2)`, resp.
`(−d, −2d)`.
-/

namespace ZInQ.RouteK.Selmer

variable {p : ℕ} [hp : Fact p.Prime]

/-- `‖d‖ = p⁻¹` for a squarefree `d` divisible by `p`. -/
theorem padic_norm_natCast_of_squarefree {d : ℕ} (hpd : p ∣ d) (hd : Squarefree d) :
    ‖(d : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  obtain ⟨m, rfl⟩ := hpd
  have hm : ¬(p : ℤ) ∣ (m : ℤ) := by
    rintro h
    have : p ∣ m := by exact_mod_cast h
    obtain ⟨k, rfl⟩ := this
    exact hp.out.not_isUnit (hd p ⟨k, by ring⟩)
  have := padic_norm_intCast_eq_one (p := p) hm
  push_cast at this ⊢
  rw [norm_mul, Padic.norm_p, this, mul_one]

/-- The norm of a nonzero square is an even power of `p`. -/
theorem padic_norm_ne_zpow_odd {z : ℚ_[p]} (hz : z ≠ 0) (h : IsSquare z) (k : ℤ) :
    ‖z‖ ≠ (p : ℝ) ^ (2 * k + 1) := by
  obtain ⟨m, hm⟩ := even_valuation_of_isSquare hz h
  rw [Padic.norm_eq_zpow_neg_valuation hz, hm]
  intro he
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have := zpow_right_injective₀ (by linarith) hp1.ne' he
  omega

/-- **Lemma B** (nt-prop0 §2.4). -/
theorem loc_padic_dvd_iff (hp2 : p ≠ 2) {d : ℕ} (hpd : p ∣ d) (hd : Squarefree d) (a b : ℤ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Loc ℚ_[p] d a b ↔ ∃ i j : ℕ, i < 2 ∧ j < 2 ∧
      IsSquare ((a * d ^ i * (-1) ^ j : ℤ) : ℚ_[p]) ∧
      IsSquare ((b * 2 ^ i * (-d) ^ j : ℤ) : ℚ_[p]) := by
  set D : ℚ_[p] := (d : ℚ_[p])
  set A : ℚ_[p] := (a : ℚ_[p])
  set B : ℚ_[p] := (b : ℚ_[p])
  have hD : ‖D‖ = (p : ℝ)⁻¹ := padic_norm_natCast_of_squarefree hpd hd
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hD0 : D ≠ 0 := by
    intro h; rw [h, norm_zero] at hD; exact (inv_pos.mpr (by linarith : (0 : ℝ) < p)).ne hD
  have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  have hA0 : A ≠ 0 := Int.cast_ne_zero.mpr ha
  have hB0 : B ≠ 0 := Int.cast_ne_zero.mpr hb
  have hn2 := padic_norm_two (p := p) hp2
  -- the casts in the statement, in terms of `A`, `B`, `D`
  have hcastA : ∀ i j : ℕ, ((a * d ^ i * (-1) ^ j : ℤ) : ℚ_[p]) = A * (D ^ i * (-1) ^ j) := by
    intro i j; simp only [A, D]; push_cast; ring
  have hcastB : ∀ i j : ℕ, ((b * 2 ^ i * (-d) ^ j : ℤ) : ℚ_[p]) = B * (2 ^ i * (-D) ^ j) := by
    intro i j; simp only [B, D]; push_cast; ring
  simp only [hcastA, hcastB]
  have hv : ∀ i j : ℕ, D ^ i * (-1) ^ j ≠ 0 := fun i j =>
    mul_ne_zero (pow_ne_zero _ hD0) (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  have hw : ∀ i j : ℕ, (2 : ℚ_[p]) ^ i * (-D) ^ j ≠ 0 := fun i j =>
    mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ (neg_ne_zero.mpr hD0))
  constructor
  swap
  · rintro ⟨i, j, hi, hj, hsa, hsb⟩
    exact loc_of_sqEq_torsion h2 hD0 hi hj ((sqEq_iff_isSquare_mul hA0 (hv i j)).mpr hsa)
      ((sqEq_iff_isSquare_mul hB0 (hw i j)).mpr hsb)
  -- `key`: it suffices to show `(A, B)` is in a torsion class
  have key : ∀ i j : ℕ, i < 2 → j < 2 → SqEq A (D ^ i * (-1) ^ j) →
      SqEq B (2 ^ i * (-D) ^ j) → ∃ i j : ℕ, i < 2 ∧ j < 2 ∧
        IsSquare (A * (D ^ i * (-1) ^ j)) ∧ IsSquare (B * (2 ^ i * (-D) ^ j)) :=
    fun i j hi hj h₁ h₂ => ⟨i, j, hi, hj, h₁.isSquare_mul, h₂.isSquare_mul⟩
  rintro (⟨⟨s, hs⟩, ⟨t, ht⟩⟩ | ⟨x, h₁, h₂, h₃⟩)
  · refine ⟨0, 0, by norm_num, by norm_num, ⟨s, by rw [hs]; ring⟩, ⟨t, by rw [ht]; ring⟩⟩
  rcases loc_torsion h2 hD0 hA0 hB0 h₁ h₂ h₃ with ⟨-, ha', hb'⟩ | ⟨-, ha', hb'⟩ | ⟨-, ha', hb'⟩ |
    ⟨hx0, hxd, hxd', hxa, hxb, hxab, hsq⟩
  · exact key 0 1 (by norm_num) (by norm_num) (by simpa using ha') (by simpa using hb')
  · exact key 1 0 (by norm_num) (by norm_num) (by simpa using ha') (by simpa using hb')
  · exact key 1 1 (by norm_num) (by norm_num) (by simpa using ha') (by simpa [mul_comm] using hb')
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  rcases lt_trichotomy ‖x‖ ‖D‖ with hlt | heq | hgt
  · -- `‖x‖ < ‖d‖`: `x − d ≡ −d`, `x + d ≡ d`, so `(a, b) ≡ (−1, −d)`
    have e₂ : SqEq (x - D) (-D) := by
      rw [show x - D = -D + x by ring]; exact sqEq_add_of_norm_lt hp2 (by rwa [norm_neg])
    have e₃ : SqEq (x + D) D := by
      rw [add_comm]; exact sqEq_add_of_norm_lt hp2 hlt
    have hb' : SqEq B (-D) := hxb.symm.trans e₂
    have hab : SqEq (A * B) D := hxab.symm.trans e₃
    have ha' : SqEq A (-1) := by
      have := sqEq_of_mul_sqEq hab hb' (neg_ne_zero.mpr hD0)
      exact (this.trans ⟨1, one_ne_zero, by ring⟩ : SqEq A (-1 * D ^ 2)).of_mul_sq hD0
    exact key 0 1 (by norm_num) (by norm_num) (by simpa using ha') (by simpa using hb')
  · -- `‖x‖ = ‖d‖`: `x = d t` with `t` a unit
    set t := x / D with ht_def
    have hxt : x = D * t := by rw [ht_def]; field_simp
    have ht1 : ‖t‖ = 1 := by
      rw [ht_def, norm_div, heq, div_self (norm_pos_iff.mpr hD0).ne']
    have hle : ∀ c : ℚ_[p], ‖c‖ = 1 → ‖t + c‖ ≤ 1 := fun c hc =>
      (Padic.nonarchimedean _ _).trans (by rw [ht1, hc, max_self])
    have hm1 : ‖(-1 : ℚ_[p])‖ = 1 := by rw [norm_neg, norm_one]
    by_cases hA : ‖t - 1‖ < 1
    · -- `t ≡ 1`, `t + 1 ≡ 2`: `(a, b) ≡ (d, 2)`
      have et : SqEq t 1 := by
        rw [show t = 1 + (t - 1) by ring]
        exact sqEq_add_of_norm_lt hp2 (by rwa [norm_one])
      have et' : SqEq (t + 1) 2 := by
        rw [show t + 1 = 2 + (t - 1) by ring]
        exact sqEq_add_of_norm_lt hp2 (by rwa [hn2])
      have ha' : SqEq A D := by
        refine hxa.symm.trans ?_
        rw [hxt]; simpa using (SqEq.refl D).mul et
      have hab : SqEq (B * A) (2 * D) := by
        rw [mul_comm]
        refine hxab.symm.trans ?_
        rw [hxt, show D * t + D = D * (t + 1) by ring, mul_comm 2 D]
        exact (SqEq.refl D).mul et'
      have hb' : SqEq B 2 := by
        have := sqEq_of_mul_sqEq hab ha' hD0
        exact (this.trans ⟨1, one_ne_zero, by ring⟩ : SqEq B (2 * D ^ 2)).of_mul_sq hD0
      exact key 1 0 (by norm_num) (by norm_num) (by simpa using ha') (by simpa using hb')
    by_cases hB : ‖t + 1‖ < 1
    · -- `t ≡ −1`, `t − 1 ≡ −2`: `(a, b) ≡ (−d, −2d)`
      have et : SqEq t (-1) := by
        rw [show t = -1 + (t + 1) by ring]
        exact sqEq_add_of_norm_lt hp2 (by rwa [hm1])
      have et' : SqEq (t - 1) (-2) := by
        rw [show t - 1 = -2 + (t + 1) by ring]
        exact sqEq_add_of_norm_lt hp2 (by rwa [norm_neg, hn2])
      have ha' : SqEq A (-D) := by
        refine hxa.symm.trans ?_
        rw [hxt]; simpa using (SqEq.refl D).mul et
      have hb' : SqEq B (-(2 * D)) := by
        refine hxb.symm.trans ?_
        rw [hxt, show D * t - D = D * (t - 1) by ring, show -(2 * D) = D * (-2) by ring]
        exact (SqEq.refl D).mul et'
      exact key 1 1 (by norm_num) (by norm_num) (by simpa using ha') (by simpa [mul_comm] using hb')
    · -- `t ∓ 1` both units: `‖x(x − d)(x + d)‖ = p⁻³`, not the norm of a square
      exfalso
      have hA1 : ‖t - 1‖ = 1 := le_antisymm (by rw [sub_eq_add_neg]; exact hle _ hm1) (not_lt.mp hA)
      have hB1 : ‖t + 1‖ = 1 := le_antisymm (hle _ norm_one) (not_lt.mp hB)
      have hz0 : x * (x - D) * (x + D) ≠ 0 := mul_ne_zero (mul_ne_zero hx0 hxd) hxd'
      apply padic_norm_ne_zpow_odd hz0 hsq (-2)
      rw [hxt, show D * t * (D * t - D) * (D * t + D) = D ^ 3 * t * (t - 1) * (t + 1) by ring,
        norm_mul, norm_mul, norm_mul, norm_pow, hD, ht1, hA1, hB1]
      norm_num
  · -- `‖x‖ > ‖d‖`: `x ± d ≡ x`, so `(a, b) ≡ (1, 1)`
    have e₂ : SqEq (x - D) x := by
      rw [sub_eq_add_neg]; exact sqEq_add_of_norm_lt hp2 (by rwa [norm_neg])
    have e₃ : SqEq (x + D) x := sqEq_add_of_norm_lt hp2 hgt
    have hb' : SqEq B x := hxb.symm.trans e₂
    have hab : SqEq (A * B) x := hxab.symm.trans e₃
    have ha' : SqEq A 1 := by
      have := sqEq_of_mul_sqEq hab hb' hx0
      exact (this.trans ⟨1, one_ne_zero, by ring⟩ : SqEq A (1 * x ^ 2)).of_mul_sq hx0
    have hb'' : SqEq B 1 := hb'.trans (hxa.trans ha')
    exact key 0 0 (by norm_num) (by norm_num) (by simpa using ha') (by simpa using hb'')

end ZInQ.RouteK.Selmer
