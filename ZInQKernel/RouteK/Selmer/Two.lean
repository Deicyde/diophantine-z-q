import ZInQKernel.RouteK.Selmer.BadOdd

/-!
# The place 2

`docs/research/nt-prop0.md` §2.5, Lemma T: for odd `d` (in particular `d ≡ 5 (mod 8)`) and nonzero
`a, b`, the covering `D_{a,b}` is soluble over `ℚ₂` iff `(a, b)` is one of the eight classes
`(d^i (−1)^j, 2^i (−d)^j 5^k)`, `i, j, k ∈ {0, 1}`: the four torsion classes and their products with
`(1, 5)`.

* (⇐) The torsion classes come from `loc_of_sqEq_torsion`. The classes with `k = 1` have the
  rational witnesses `x = 1/4`, `d(1 + 4d)/(1 − 4d)`, `−4d²`, `−d(1 − 4d)/(1 + 4d)` of the table in
  §2.5 (`loc_two_adic_five`), checked by the 2-adic rational test.
* (⇒) After (Tor), split on `v = v₂(x)`. For `v ≤ −3` and `v ≥ 3`, (P) gives `(1, 1)` and
  `(−1, −d)`. For `v = ±1` the norm of `x(x − d)(x + d)` is an odd power of `2`. For `v = ±2`,
  `x ∓ d ≡ 5x`, resp. `x − d ≡ −5d`, `x + d ≡ 5d`. For `v = 0`, one of `x ∓ d` has norm `1/2` and
  the other norm at most `1/8`; this gives `x ≡ ±d` and `x ∓ d ≡ ∓2d` or `∓10d`.

Only "two 2-adic numbers of the same norm have a sum of smaller norm" (`two_adic_norm_add_lt`), the
discreteness of the norm and (P) are used; no residues mod 8 appear explicitly.
-/

namespace ZInQ.RouteK.Selmer

/-! ### Norms in `ℚ₂` -/

theorem two_adic_norm_eq_zpow {z : ℚ_[2]} (hz : z ≠ 0) : ‖z‖ = (2 : ℝ) ^ (-z.valuation) := by
  rw [Padic.norm_eq_zpow_neg_valuation hz]; norm_num

/-- Discreteness of the 2-adic norm: `‖z‖ < 2^k` gives `‖z‖ ≤ 2^(k − 1)`. -/
theorem two_adic_norm_le_of_lt {z : ℚ_[2]} {k : ℤ} (h : ‖z‖ < (2 : ℝ) ^ k) :
    ‖z‖ ≤ (2 : ℝ) ^ (k - 1) := by
  have := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one z k).mp (by exact_mod_cast h)
  exact_mod_cast this

theorem two_adic_norm_intCast_of_odd {c : ℤ} (hc : Odd c) : ‖(c : ℚ_[2])‖ = 1 :=
  padic_norm_intCast_eq_one (by
    rw [Nat.cast_ofNat, ← even_iff_two_dvd, Int.not_even_iff_odd]; exact hc)

theorem two_adic_norm_natCast_of_odd {d : ℕ} (hd : Odd d) : ‖(d : ℚ_[2])‖ = 1 := by
  have := two_adic_norm_intCast_of_odd (c := d) (by exact_mod_cast hd)
  simpa using this

theorem two_adic_norm_four : ‖(4 : ℚ_[2])‖ = 1 / 4 := by
  rw [show (4 : ℚ_[2]) = 2 ^ 2 by norm_num, norm_pow, two_adic_norm_two]; norm_num

theorem two_adic_norm_five : ‖(5 : ℚ_[2])‖ = 1 := by
  have := two_adic_norm_intCast_of_odd (c := 5) ⟨2, rfl⟩
  simpa using this

/-- A 2-adic number of norm `1` is `≡ 1 (mod 2)`: `‖1 + t‖ < 1`. -/
theorem two_adic_norm_one_add_lt {t : ℚ_[2]} (ht : ‖t‖ = 1) : ‖1 + t‖ < 1 := by
  set T : ℤ_[2] := ⟨t, ht.le⟩
  have hT : PadicInt.toZMod T ≠ 0 := by
    intro h0
    have := norm_lt_one_of_toZMod_eq_zero h0
    rw [PadicInt.norm_def] at this
    change ‖t‖ < 1 at this
    rw [ht] at this; exact lt_irrefl _ this
  have h1 : PadicInt.toZMod (1 + T) = 0 := by
    rw [map_add, map_one]
    generalize PadicInt.toZMod T = z at hT
    revert z; decide
  have := norm_lt_one_of_toZMod_eq_zero h1
  rwa [PadicInt.norm_def, PadicInt.coe_add, PadicInt.coe_one] at this

/-- Two elements of `ℚ₂` of the same nonzero norm have a sum of smaller norm. -/
theorem two_adic_norm_add_lt {u w : ℚ_[2]} (hw : w ≠ 0) (h : ‖u‖ = ‖w‖) : ‖u + w‖ < ‖w‖ := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have ht : ‖u / w‖ = 1 := by rw [norm_div, h, div_self hwn.ne']
  have := two_adic_norm_one_add_lt ht
  have e : u + w = w * (1 + u / w) := by field_simp; ring
  rw [e, norm_mul]
  nlinarith

/-- **(P)** at `2` in the form `‖y‖ < ‖x‖/4` (`‖2‖² = 1/4`). -/
theorem sqEq_add_two_adic {x y : ℚ_[2]} (h : ‖y‖ < ‖x‖ / 4) : SqEq (x + y) x :=
  sqEq_add_of_norm_lt_two_sq (by rw [two_adic_norm_two]; linarith)

theorem SqEq.trans_eq {K : Type*} [Field K] {u v w : K} (h : SqEq u v) (e : v = w) : SqEq u w :=
  e ▸ h

theorem sqEq_one_of_isSquare {K : Type*} [Field K] {u : K} (hu : u ≠ 0) (h : IsSquare u) :
    SqEq u 1 := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := by rintro rfl; exact hu (mul_zero 0)
  exact ⟨r, hr, by ring⟩

/-- A 2-adic unit `≡ 1 (mod 4)` is `≡ 1` or `≡ 5` in `ℚ₂*/ℚ₂*²`, in the form: if
`‖y‖ ≤ ‖x‖/4` then `x + y ≡ x` or `x + y ≡ 5x`. -/
theorem sqEq_add_or_five_two_adic {x y : ℚ_[2]} (hx : x ≠ 0) (h : ‖y‖ ≤ ‖x‖ / 4) :
    SqEq (x + y) x ∨ SqEq (x + y) (5 * x) := by
  by_cases h' : ‖y‖ < ‖x‖ / 4
  · exact Or.inl (sqEq_add_two_adic h')
  right
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h4 : (4 : ℚ_[2]) * x ≠ 0 := mul_ne_zero (by norm_num) hx
  have hy : ‖y‖ = ‖-(4 * x)‖ := by
    rw [norm_neg, norm_mul, two_adic_norm_four]; linarith [not_lt.mp h']
  have := two_adic_norm_add_lt (neg_ne_zero.mpr h4) hy
  rw [norm_neg, norm_mul, two_adic_norm_four] at this
  rw [show x + y = 5 * x + (y + -(4 * x)) by ring]
  refine sqEq_add_two_adic ?_
  rw [norm_mul, two_adic_norm_five]
  linarith

/-- Closes the identities `q = m / n * c²` of the witness table. -/
local macro "wit" : tactic =>
  `(tactic| first | (push_cast; field_simp; done) | (push_cast; field_simp; ring))

/-! ### Sufficiency: the witnesses for the classes with `k = 1` -/

/-- The four classes `(d^i (−1)^j, 2^i (−d)^j · 5)` are soluble over `ℚ₂` (the table of §2.5,
witnesses `x = 1/4`, `d(1 + 4d)/(1 − 4d)`, `−4d²`, `−d(1 − 4d)/(1 + 4d)`). -/
theorem loc_two_adic_five {d : ℕ} (hd : Odd d) {i j : ℕ} (hi : i < 2) (hj : j < 2) :
    Loc ℚ_[2] d ((d : ℚ_[2]) ^ i * (-1) ^ j) (2 ^ i * (-(d : ℚ_[2])) ^ j * 5) := by
  obtain ⟨e, he⟩ := hd
  have sq : ∀ (m n : ℤ) (c q : ℚ_[2]), n % 2 = 1 → m % 8 = n % 8 →
      q = (m : ℚ_[2]) / n * c ^ 2 → IsSquare q := fun m n c q hn h hq =>
    hq ▸ (isSquare_intCast_div_two_adic (Int.odd_iff.mpr hn) h).mul (IsSquare.sq c)
  have hd0 : (d : ℚ_[2]) ≠ 0 := by
    have : d ≠ 0 := by omega
    exact_mod_cast this
  have hm : (1 : ℚ_[2]) - 4 * d ≠ 0 := by
    have : (1 - 4 * (d : ℤ)) ≠ 0 := by omega
    exact_mod_cast this
  have hp : (1 : ℚ_[2]) + 4 * d ≠ 0 := by
    have : (1 + 4 * (d : ℤ)) ≠ 0 := by omega
    exact_mod_cast this
  have hm' : (1 : ℚ_[2]) - d * 4 ≠ 0 := by rwa [mul_comm]
  have hp' : (1 : ℚ_[2]) + d * 4 ≠ 0 := by rwa [mul_comm]
  interval_cases i <;> interval_cases j <;> simp only [pow_zero, pow_one, one_mul, mul_one]
  · -- `(1, 5)`, `x = 1/4`
    refine Or.inr ⟨1 / 4, ⟨1 / 2, by norm_num⟩, ?_, ?_⟩
    · exact sq (1 - 4 * d) 5 (1 / 2) _ rfl (by omega) (by wit)
    · exact sq (1 + 4 * d) 5 (1 / 2) _ rfl (by omega) (by wit)
  · -- `(−1, −5d)`, `x = −4d²`
    refine Or.inr ⟨-4 * d ^ 2, ⟨2 * d, by field_simp; ring⟩, ?_, ?_⟩
    · exact sq (1 + 4 * d) 5 1 _ rfl (by omega) (by wit)
    · exact sq (1 - 4 * d) 5 1 _ rfl (by omega) (by wit)
  · -- `(d, 10)`, `x = d(1 + 4d)/(1 − 4d)`
    refine Or.inr ⟨d * (1 + 4 * d) / (1 - 4 * d), ?_, ?_, ?_⟩
    · exact sq (1 + 4 * d) (1 - 4 * d) 1 _ (by omega) (by omega)
        (by wit)
    · exact sq 1 (5 * (1 - 4 * d)) (2 * d) _ (by omega) (by omega)
        (by wit)
    · exact sq 1 (5 * (1 - 4 * d)) 1 _ (by omega) (by omega)
        (by wit)
  · -- `(−d, −10d)`, `x = −d(1 − 4d)/(1 + 4d)`
    refine Or.inr ⟨-d * (1 - 4 * d) / (1 + 4 * d), ?_, ?_, ?_⟩
    · exact sq (1 - 4 * d) (1 + 4 * d) 1 _ (by omega) (by omega)
        (by wit)
    · exact sq 1 (5 * (1 + 4 * d)) 1 _ (by omega) (by omega)
        (by wit)
    · exact sq 1 (5 * (1 + 4 * d)) 2 _ (by omega) (by omega)
        (by wit)

/-! ### Lemma T -/

/-- **Lemma T** (nt-prop0 §2.5), for any odd `d`: the covering of `(a, b)` is soluble over `ℚ₂`
iff `a d^i (−1)^j` and `b 2^i (−d)^j 5^k` are squares for some `i, j, k ∈ {0, 1}`. -/
theorem loc_two_adic_iff_of_odd {d : ℕ} (hd : Odd d) (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Loc ℚ_[2] d a b ↔ ∃ i j k : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧
      IsSquare ((a * d ^ i * (-1) ^ j : ℤ) : ℚ_[2]) ∧
      IsSquare ((b * 2 ^ i * (-d) ^ j * 5 ^ k : ℤ) : ℚ_[2]) := by
  set D : ℚ_[2] := (d : ℚ_[2])
  set A : ℚ_[2] := (a : ℚ_[2])
  set B : ℚ_[2] := (b : ℚ_[2])
  have hD : ‖D‖ = 1 := two_adic_norm_natCast_of_odd hd
  have hD0 : D ≠ 0 := by intro h; rw [h, norm_zero] at hD; exact zero_ne_one hD
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  have hA0 : A ≠ 0 := Int.cast_ne_zero.mpr ha
  have hB0 : B ≠ 0 := Int.cast_ne_zero.mpr hb
  have hn2 := two_adic_norm_two
  have hn5 := two_adic_norm_five
  have hcastA : ∀ i j : ℕ, ((a * d ^ i * (-1) ^ j : ℤ) : ℚ_[2]) = A * (D ^ i * (-1) ^ j) := by
    intro i j; simp only [A, D]; push_cast; ring
  have hcastB : ∀ i j k : ℕ, ((b * 2 ^ i * (-d) ^ j * 5 ^ k : ℤ) : ℚ_[2]) =
      B * (2 ^ i * (-D) ^ j * 5 ^ k) := by
    intro i j k; simp only [B, D]; push_cast; ring
  simp only [hcastA, hcastB]
  have hv : ∀ i j : ℕ, D ^ i * (-1) ^ j ≠ 0 := fun i j =>
    mul_ne_zero (pow_ne_zero _ hD0) (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  have hw : ∀ i j k : ℕ, (2 : ℚ_[2]) ^ i * (-D) ^ j * 5 ^ k ≠ 0 := fun i j k =>
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ (neg_ne_zero.mpr hD0)))
      (pow_ne_zero _ (by norm_num))
  constructor
  swap
  · rintro ⟨i, j, k, hi, hj, hk, hsa, hsb⟩
    have ha' := (sqEq_iff_isSquare_mul hA0 (hv i j)).mpr hsa
    have hb' := (sqEq_iff_isSquare_mul hB0 (hw i j k)).mpr hsb
    interval_cases k
    · exact loc_of_sqEq_torsion h2 hD0 hi hj ha' (hb'.trans_eq (by ring))
    · rw [loc_congr_sq ha' (hb'.trans_eq (by ring) : SqEq B (2 ^ i * (-D) ^ j * 5))]
      exact loc_two_adic_five hd hi hj
  -- `key`: it suffices to show `(A, B)` is in one of the eight classes
  have key : ∀ i j k : ℕ, i < 2 → j < 2 → k < 2 → SqEq A (D ^ i * (-1) ^ j) →
      SqEq B (2 ^ i * (-D) ^ j * 5 ^ k) → ∃ i j k : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧
        IsSquare (A * (D ^ i * (-1) ^ j)) ∧ IsSquare (B * (2 ^ i * (-D) ^ j * 5 ^ k)) :=
    fun i j k hi hj hk h₁ h₂ => ⟨i, j, k, hi, hj, hk, h₁.isSquare_mul, h₂.isSquare_mul⟩
  rintro (⟨⟨s, hs⟩, ⟨t, ht⟩⟩ | ⟨x, h₁, h₂, h₃⟩)
  · exact ⟨0, 0, 0, by norm_num, by norm_num, by norm_num, ⟨s, by rw [hs]; ring⟩,
      ⟨t, by rw [ht]; ring⟩⟩
  rcases loc_torsion h2 hD0 hA0 hB0 h₁ h₂ h₃ with ⟨-, ha', hb'⟩ | ⟨-, ha', hb'⟩ | ⟨-, ha', hb'⟩ |
    ⟨hx0, hxd, hxd', hxa, hxb, hxab, hsq⟩
  · exact key 0 1 0 (by norm_num) (by norm_num) (by norm_num) (ha'.trans_eq (by ring))
      (hb'.trans_eq (by ring))
  · exact key 1 0 0 (by norm_num) (by norm_num) (by norm_num) (ha'.trans_eq (by ring))
      (hb'.trans_eq (by ring))
  · exact key 1 1 0 (by norm_num) (by norm_num) (by norm_num) (ha'.trans_eq (by ring))
      (hb'.trans_eq (by ring))
  have hz0 : x * (x - D) * (x + D) ≠ 0 := mul_ne_zero (mul_ne_zero hx0 hxd) hxd'
  have hodd := padic_norm_ne_zpow_odd hz0 hsq
  have hznorm : ‖x * (x - D) * (x + D)‖ = ‖x‖ * ‖x - D‖ * ‖x + D‖ := by
    rw [norm_mul, norm_mul]
  -- the product is a nonzero square
  have hprod : SqEq (x * (x - D) * (x + D)) 1 := sqEq_one_of_isSquare hz0 hsq
  have hxn := two_adic_norm_eq_zpow hx0
  set v := x.valuation with hv_def
  rcases (by omega : v ≤ -3 ∨ v = -2 ∨ v = -1 ∨ v = 0 ∨ v = 1 ∨ v = 2 ∨ 3 ≤ v) with
    hv | hv | hv | hv | hv | hv | hv
  · -- `v ≤ −3`: `x ∓ d ≡ x`, so `(a, b) ≡ (1, 1)`
    have h8 : (8 : ℝ) ≤ ‖x‖ := by
      rw [hxn]
      calc (8 : ℝ) = 2 ^ (3 : ℤ) := by norm_num
        _ ≤ 2 ^ (-v) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have e₂ : SqEq (x - D) x := by
      rw [sub_eq_add_neg]
      exact sqEq_add_of_norm_le_two_adic (by rw [norm_neg, hD]; linarith)
    have e₃ : SqEq (x + D) x := sqEq_add_of_norm_le_two_adic (by rw [hD]; linarith)
    have hb' : SqEq B x := hxb.symm.trans e₂
    have hab : SqEq (A * B) x := hxab.symm.trans e₃
    have ha' : SqEq A 1 :=
      ((sqEq_of_mul_sqEq hab hb' hx0).trans_eq (by ring) : SqEq A (1 * x ^ 2)).of_mul_sq hx0
    exact key 0 0 0 (by norm_num) (by norm_num) (by norm_num) (ha'.trans_eq (by ring))
      ((hb'.trans (hxa.trans ha')).trans_eq (by ring))
  · -- `v = −2`: `x ∓ d ≡ 5x`, so `x ≡ 1` and `(a, b) ≡ (1, 5)`
    have h4 : ‖x‖ = 4 := by rw [hxn, hv]; norm_num
    have h4x : ‖4 * x‖ = 1 := by rw [norm_mul, two_adic_norm_four, h4]; norm_num
    have l₁ := two_adic_norm_add_lt hD0 (h4x.trans hD.symm)
    have l₂ := two_adic_norm_add_lt hD0 ((norm_neg (4 * x)).trans (h4x.trans hD.symm))
    have e₂ : SqEq (x - D) (5 * x) := by
      rw [show x - D = 5 * x + -(4 * x + D) by ring]
      refine sqEq_add_two_adic ?_
      rw [norm_neg, norm_mul, hn5, h4]; linarith
    have e₃ : SqEq (x + D) (5 * x) := by
      rw [show x + D = 5 * x + (-(4 * x) + D) by ring]
      refine sqEq_add_two_adic ?_
      rw [norm_mul, hn5, h4]; linarith
    have h5x : 5 * x ≠ 0 := mul_ne_zero (by norm_num) hx0
    have ex : SqEq x 1 := by
      have := (((SqEq.refl x).mul e₂).mul e₃).symm.trans hprod
      exact ((this.symm.trans_eq (by ring) : SqEq 1 (x * (5 * x) ^ 2)).of_mul_sq h5x).symm
    have ha' : SqEq A 1 := hxa.symm.trans ex
    have hb' : SqEq B (5 * 1) := hxb.symm.trans (e₂.trans ((SqEq.refl 5).mul ex))
    exact key 0 0 1 (by norm_num) (by norm_num) (by norm_num) (ha'.trans_eq (by ring))
      (hb'.trans_eq (by ring))
  · -- `v = −1`: `‖x(x − d)(x + d)‖ = 8`
    exfalso
    have h2x : ‖x‖ = 2 := by rw [hxn, hv]; norm_num
    have n₂ : ‖x - D‖ = 2 := by
      rw [sub_eq_add_neg, Padic.add_eq_max_of_ne (by rw [norm_neg, hD, h2x]; norm_num),
        norm_neg, hD, h2x]; norm_num
    have n₃ : ‖x + D‖ = 2 := by
      rw [Padic.add_eq_max_of_ne (by rw [hD, h2x]; norm_num), hD, h2x]; norm_num
    apply hodd 1
    rw [hznorm, h2x, n₂, n₃]; norm_num
  · -- `v = 0`
    have h1x : ‖x‖ = 1 := by rw [hxn, hv]; norm_num
    have hP : ‖x - D‖ < 1 := by
      have := two_adic_norm_add_lt (neg_ne_zero.mpr hD0) (by rw [norm_neg, hD, h1x] : ‖x‖ = ‖-D‖)
      rwa [← sub_eq_add_neg, norm_neg, hD] at this
    have hQ : ‖x + D‖ < 1 := by
      have := two_adic_norm_add_lt hD0 (by rw [hD, h1x] : ‖x‖ = ‖D‖)
      rwa [hD] at this
    -- discreteness: `< 2^k` gives `≤ 2^(k-1)`
    have disc : ∀ (z : ℚ_[2]) (k : ℤ) (r : ℝ), ‖z‖ < (2 : ℝ) ^ k → (2 : ℝ) ^ (k - 1) = r →
        ‖z‖ ≤ r := fun z k r h e => e ▸ two_adic_norm_le_of_lt h
    have h2D : ‖2 * D‖ = 1 / 2 := by rw [norm_mul, hn2, hD]; norm_num
    have hdiff : (x + D) + -(x - D) = 2 * D := by ring
    have hP2 : ‖x - D‖ ≤ 1 / 2 := disc _ 0 _ (by simpa using hP) (by norm_num)
    have hQ2 : ‖x + D‖ ≤ 1 / 2 := disc _ 0 _ (by simpa using hQ) (by norm_num)
    by_cases hPh : ‖x - D‖ < 1 / 2
    · -- `‖x + d‖ = 1/2` and `‖x − d‖ ≤ 1/8`: `x ≡ d`, `x + d ≡ 2d` or `10d`
      have hQe : ‖x + D‖ = 1 / 2 := by
        refine le_antisymm hQ2 (not_lt.mp fun hQh => ?_)
        have := (Padic.nonarchimedean (x + D) (-(x - D))).trans_lt
          (max_lt hQh (by rwa [norm_neg]))
        rw [hdiff, h2D] at this; exact lt_irrefl _ this
      have hP4 : ‖x - D‖ ≤ 1 / 4 := disc _ (-1) _ (by norm_num; linarith) (by norm_num)
      have hP8 : ‖x - D‖ ≤ 1 / 8 := by
        refine disc _ (-2) _ (lt_of_le_of_ne (by norm_num; linarith) fun he => hodd (-2) ?_)
          (by norm_num)
        rw [hznorm, h1x, hQe, he]; norm_num
      have ex : SqEq x D := by
        have := sqEq_add_of_norm_le_two_adic (x := D) (y := x - D) (by rw [hD]; linarith)
        rwa [show D + (x - D) = x by ring] at this
      have ha' : SqEq A D := hxa.symm.trans ex
      have hQ' : SqEq (x + D) (2 * D) ∨ SqEq (x + D) (5 * (2 * D)) := by
        have := sqEq_add_or_five_two_adic (x := 2 * D) (y := x - D) (mul_ne_zero h2 hD0)
          (by rw [h2D]; linarith)
        rwa [show 2 * D + (x - D) = x + D by ring] at this
      rcases hQ' with hQ' | hQ'
      · have hab : SqEq (B * A) (2 * D) := by
          rw [mul_comm]; exact hxab.symm.trans hQ'
        have hb' : SqEq B 2 :=
          ((sqEq_of_mul_sqEq hab ha' hD0).trans_eq (by ring) : SqEq B (2 * D ^ 2)).of_mul_sq hD0
        exact key 1 0 0 (by norm_num) (by norm_num) (by norm_num) (ha'.trans_eq (by ring))
          (hb'.trans_eq (by ring))
      · have hab : SqEq (B * A) (10 * D) := by
          rw [mul_comm]; exact (hxab.symm.trans hQ').trans_eq (by ring)
        have hb' : SqEq B 10 :=
          ((sqEq_of_mul_sqEq hab ha' hD0).trans_eq (by ring) : SqEq B (10 * D ^ 2)).of_mul_sq hD0
        exact key 1 0 1 (by norm_num) (by norm_num) (by norm_num) (ha'.trans_eq (by ring))
          (hb'.trans_eq (by ring))
    · -- `‖x − d‖ = 1/2` and `‖x + d‖ ≤ 1/8`: `x ≡ −d`, `x − d ≡ −2d` or `−10d`
      have hPe : ‖x - D‖ = 1 / 2 := le_antisymm hP2 (not_lt.mp hPh)
      have hQh : ‖x + D‖ < 1 / 2 := by
        refine lt_of_le_of_ne hQ2 fun hQe => ?_
        have := two_adic_norm_add_lt (u := x + D) (w := -(x - D))
          (neg_ne_zero.mpr hxd) (by rw [norm_neg, hQe, hPe])
        rw [hdiff, h2D, norm_neg, hPe] at this; exact lt_irrefl _ this
      have hQ4 : ‖x + D‖ ≤ 1 / 4 := disc _ (-1) _ (by norm_num; linarith) (by norm_num)
      have hQ8 : ‖x + D‖ ≤ 1 / 8 := by
        refine disc _ (-2) _ (lt_of_le_of_ne (by norm_num; linarith) fun he => hodd (-2) ?_)
          (by norm_num)
        rw [hznorm, h1x, hPe, he]; norm_num
      have ex : SqEq x (-D) := by
        have := sqEq_add_of_norm_le_two_adic (x := -D) (y := x + D)
          (by rw [norm_neg, hD]; linarith)
        rwa [show -D + (x + D) = x by ring] at this
      have ha' : SqEq A (-D) := hxa.symm.trans ex
      have hP' : SqEq (x - D) (-(2 * D)) ∨ SqEq (x - D) (5 * -(2 * D)) := by
        have := sqEq_add_or_five_two_adic (x := -(2 * D)) (y := x + D)
          (neg_ne_zero.mpr (mul_ne_zero h2 hD0)) (by rw [norm_neg, h2D]; linarith)
        rwa [show -(2 * D) + (x + D) = x - D by ring] at this
      rcases hP' with hP' | hP'
      · exact key 1 1 0 (by norm_num) (by norm_num) (by norm_num) (ha'.trans_eq (by ring))
          ((hxb.symm.trans hP').trans_eq (by ring))
      · exact key 1 1 1 (by norm_num) (by norm_num) (by norm_num) (ha'.trans_eq (by ring))
          ((hxb.symm.trans hP').trans_eq (by ring))
  · -- `v = 1`: `‖x(x − d)(x + d)‖ = 1/2`
    exfalso
    have h2x : ‖x‖ = 1 / 2 := by rw [hxn, hv]; norm_num
    have n₂ : ‖x - D‖ = 1 := by
      rw [sub_eq_add_neg, Padic.add_eq_max_of_ne (by rw [norm_neg, hD, h2x]; norm_num),
        norm_neg, hD, h2x]; norm_num
    have n₃ : ‖x + D‖ = 1 := by
      rw [Padic.add_eq_max_of_ne (by rw [hD, h2x]; norm_num), hD, h2x]; norm_num
    apply hodd (-1)
    rw [hznorm, h2x, n₂, n₃]; norm_num
  · -- `v = 2`: `x − d ≡ −5d`, `x + d ≡ 5d`, so `(a, b) ≡ (−1, −5d)`
    have h4 : ‖x‖ = 1 / 4 := by rw [hxn, hv]; norm_num
    have h4D : ‖4 * D‖ = 1 / 4 := by rw [norm_mul, two_adic_norm_four, hD]; norm_num
    have h4D0 : 4 * D ≠ 0 := mul_ne_zero (by norm_num) hD0
    have l₁ := two_adic_norm_add_lt h4D0 (h4.trans h4D.symm)
    have l₂ := two_adic_norm_add_lt (neg_ne_zero.mpr h4D0)
      (h4.trans (h4D.symm.trans (norm_neg _).symm))
    rw [norm_neg] at l₂
    have e₂ : SqEq (x - D) (-(5 * D)) := by
      rw [show x - D = -(5 * D) + (x + 4 * D) by ring]
      refine sqEq_add_two_adic ?_
      rw [norm_neg, norm_mul, hn5, hD]; linarith
    have e₃ : SqEq (x + D) (5 * D) := by
      rw [show x + D = 5 * D + (x + -(4 * D)) by ring]
      refine sqEq_add_two_adic ?_
      rw [norm_mul, hn5, hD]; linarith
    have hb' : SqEq B (-(5 * D)) := hxb.symm.trans e₂
    have hab : SqEq (A * B) (5 * D) := hxab.symm.trans e₃
    have h5D : -(5 * D) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (by norm_num) hD0)
    have ha' : SqEq A (-1) :=
      ((sqEq_of_mul_sqEq hab hb' h5D).trans_eq (by ring) : SqEq A (-1 * (5 * D) ^ 2)).of_mul_sq
        (mul_ne_zero (by norm_num) hD0)
    exact key 0 1 1 (by norm_num) (by norm_num) (by norm_num) (ha'.trans_eq (by ring))
      (hb'.trans_eq (by ring))
  · -- `v ≥ 3`: `x − d ≡ −d`, `x + d ≡ d`, so `(a, b) ≡ (−1, −d)`
    have h8 : ‖x‖ ≤ 1 / 8 := by
      rw [hxn]
      calc (2 : ℝ) ^ (-v) ≤ 2 ^ (-3 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 1 / 8 := by norm_num
    have e₂ : SqEq (x - D) (-D) := by
      rw [show x - D = -D + x by ring]
      exact sqEq_add_of_norm_le_two_adic (by rw [norm_neg, hD]; linarith)
    have e₃ : SqEq (x + D) D := by
      rw [add_comm]; exact sqEq_add_of_norm_le_two_adic (by rw [hD]; linarith)
    have hb' : SqEq B (-D) := hxb.symm.trans e₂
    have hab : SqEq (A * B) D := hxab.symm.trans e₃
    have ha' : SqEq A (-1) :=
      ((sqEq_of_mul_sqEq hab hb' (neg_ne_zero.mpr hD0)).trans_eq (by ring) :
        SqEq A (-1 * D ^ 2)).of_mul_sq hD0
    exact key 0 1 0 (by norm_num) (by norm_num) (by norm_num) (ha'.trans_eq (by ring))
      (hb'.trans_eq (by ring))

/-- **Lemma T** (nt-prop0 §2.5) for `d ≡ 5 (mod 8)`, in the shape of `loc_padic_dvd_iff`. -/
theorem loc_two_adic_iff {d : ℕ} (hd8 : d % 8 = 5) (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Loc ℚ_[2] d a b ↔ ∃ i j k : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧
      IsSquare ((a * d ^ i * (-1) ^ j : ℤ) : ℚ_[2]) ∧
      IsSquare ((b * 2 ^ i * (-d) ^ j * 5 ^ k : ℤ) : ℚ_[2]) :=
  loc_two_adic_iff_of_odd (Nat.odd_iff.mpr (by omega)) a b ha hb

end ZInQ.RouteK.Selmer
