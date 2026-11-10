import ZInQKernel.RouteK.Selmer.Covering

/-!
# Squares in `ℚ_p`

`docs/research/nt-prop0.md` §2.1, Lemma SQ and its two consequences.

* `isSquare_of_norm_sub_one_lt`: Hensel's lemma for `X² − u` at `1`. A `p`-adic number with
  `‖u − 1‖ < ‖2‖²` is a square (`‖2‖ = 1` for odd `p`, `‖2‖ = 1/2` for `p = 2`).
* **(P)** `sqEq_add_of_norm_lt` (odd `p`: `‖y‖ < ‖x‖` gives `x + y ≡ x`) and
  `sqEq_add_of_norm_le_two_adic` (`p = 2`: `‖y‖ ≤ ‖x‖/8` gives `x + y ≡ x`).
* **SQ** `isSquare_padic_iff` (odd `p`) and `isSquare_two_adic_iff`: a nonzero `x = p^v u`, with
  `u = unitPart x` a unit of `ℤ_p`, is a square iff `v` is even and the residue of `u` is a square
  (respectively `u ≡ 1 (mod 8)`).
* **(RT)** `isSquare_intCast_div_of_residue`, `isSquare_ratCast_of_residue` (odd `p`) and
  `isSquare_intCast_div_two_adic`, `isSquare_ratCast_two_adic` (`p = 2`).
-/

namespace ZInQ.RouteK.Selmer

open Polynomial PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

theorem padic_norm_two_le_one : ‖(2 : ℚ_[p])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := p) 2

/-- For odd `p`, `2` is a `p`-adic unit. -/
theorem padic_norm_two (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  refine le_antisymm padic_norm_two_le_one (not_lt.mp fun h => hp2 ?_)
  have h' : ‖((2 : ℤ) : ℚ_[p])‖ < 1 := by simpa using h
  rw [Padic.norm_intCast_lt_one_iff] at h'
  have : p ∣ 2 := by exact_mod_cast h'
  exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this

theorem two_adic_norm_two : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
  have := Padic.norm_p (p := 2)
  rw [one_div]; exact_mod_cast this

/-- Hensel's lemma for `X² − u` at `1`: a `p`-adic number with `‖u − 1‖ < ‖2‖²` is a square. -/
theorem isSquare_of_norm_sub_one_lt {u : ℚ_[p]} (h : ‖u - 1‖ < ‖(2 : ℚ_[p])‖ ^ 2) :
    IsSquare u := by
  have h2 := padic_norm_two_le_one (p := p)
  have h1 : ‖u - 1‖ < 1 := h.trans_le (by nlinarith [norm_nonneg (2 : ℚ_[p])])
  have hu : ‖u‖ ≤ 1 := by
    have : u = (u - 1) + 1 := by ring
    rw [this]
    exact (Padic.nonarchimedean _ _).trans (max_le h1.le (by simp))
  set U : ℤ_[p] := ⟨u, hu⟩
  set F : Polynomial ℤ_[p] := X ^ 2 - C U
  have hF1 : F.aeval (1 : ℤ_[p]) = 1 - U := by simp [F]
  have hD1 : F.derivative.aeval (1 : ℤ_[p]) = 2 := by simp [F]; norm_num
  have hnorm : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hF1, hD1, PadicInt.norm_def, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one,
      norm_sub_rev]
    exact_mod_cast h
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  have hz' : z ^ 2 - U = 0 := by simpa [F] using hz
  have : ((z ^ 2 - U : ℤ_[p]) : ℚ_[p]) = 0 := by rw [hz']; rfl
  push_cast at this
  linear_combination -this

/-- A general form of **(P)**: `‖y‖ < ‖2‖² ‖x‖` gives `x + y ≡ x`. -/
theorem sqEq_add_of_norm_lt_two_sq {x y : ℚ_[p]} (h : ‖y‖ < ‖(2 : ℚ_[p])‖ ^ 2 * ‖x‖) :
    SqEq (x + y) x := by
  have hx : x ≠ 0 := by
    rintro rfl; simp only [norm_zero, mul_zero] at h; exact (norm_nonneg y).not_gt h
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsq : IsSquare ((x + y) / x) := by
    refine isSquare_of_norm_sub_one_lt ?_
    rw [show (x + y) / x - 1 = y / x by field_simp; ring, norm_div, div_lt_iff₀ hxn]
    exact h
  obtain ⟨s, hs⟩ := hsq
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : x + y = 0 := by
      rw [mul_zero, div_eq_zero_iff, or_iff_left hx] at hs; exact hs
    have hy : y = -x := by linear_combination this
    rw [hy, norm_neg] at h
    have : ‖(2 : ℚ_[p])‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) padic_norm_two_le_one
    nlinarith
  exact ⟨s, hs0, by rw [sq, ← hs]; field_simp⟩

/-- **(P)** for odd `p`: if `‖y‖ < ‖x‖` then `x + y ≡ x`. -/
theorem sqEq_add_of_norm_lt (hp2 : p ≠ 2) {x y : ℚ_[p]} (h : ‖y‖ < ‖x‖) : SqEq (x + y) x :=
  sqEq_add_of_norm_lt_two_sq (by rw [padic_norm_two hp2, one_pow, one_mul]; exact h)

/-- **(P)** for `p = 2`: if `‖y‖ ≤ ‖x‖/8` then `x + y ≡ x`. -/
theorem sqEq_add_of_norm_le_two_adic {x y : ℚ_[2]} (h : ‖y‖ ≤ ‖x‖ / 8) : SqEq (x + y) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · have : y = 0 := norm_eq_zero.mp (le_antisymm (by rw [norm_zero, zero_div] at h; exact h)
      (norm_nonneg y))
    subst this; exact ⟨1, one_ne_zero, by ring⟩
  refine sqEq_add_of_norm_lt_two_sq ?_
  rw [two_adic_norm_two]
  have := norm_pos_iff.mpr hx
  linarith

/-- A square has even valuation. -/
theorem even_valuation_of_isSquare {x : ℚ_[p]} (hx : x ≠ 0) (h : IsSquare x) :
    Even x.valuation := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := by rintro rfl; exact hx (mul_zero 0)
  exact ⟨r.valuation, Padic.valuation_mul hr hr⟩

/-! ### The unit part -/

theorem norm_unitPart_le (x : ℚ_[p]) : ‖x * (p : ℚ_[p]) ^ (-x.valuation)‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hx, neg_neg,
    ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero), neg_add_cancel, zpow_zero]

/-- The unit part `u` of `x = p^{v(x)} u` (`0` for `x = 0`). -/
noncomputable def unitPart (x : ℚ_[p]) : ℤ_[p] :=
  ⟨x * (p : ℚ_[p]) ^ (-x.valuation), norm_unitPart_le x⟩

theorem unitPart_spec (x : ℚ_[p]) : x = (p : ℚ_[p]) ^ x.valuation * unitPart x := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  change x = (p : ℚ_[p]) ^ x.valuation * (x * (p : ℚ_[p]) ^ (-x.valuation))
  rw [mul_left_comm, ← zpow_add₀ hp0, add_neg_cancel, zpow_zero, mul_one]

theorem norm_unitPart {x : ℚ_[p]} (hx : x ≠ 0) : ‖unitPart x‖ = 1 := by
  rw [PadicInt.norm_def]
  change ‖x * (p : ℚ_[p]) ^ (-x.valuation)‖ = 1
  rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hx, neg_neg,
    ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero), neg_add_cancel, zpow_zero]

theorem isUnit_unitPart {x : ℚ_[p]} (hx : x ≠ 0) : IsUnit (unitPart x) :=
  PadicInt.isUnit_iff.mpr (norm_unitPart hx)

/-- Lemma SQ(c): a nonzero `x` is a square iff `v(x)` is even and its unit part is a square. -/
theorem isSquare_iff_even_valuation {x : ℚ_[p]} (hx : x ≠ 0) :
    IsSquare x ↔ Even x.valuation ∧ IsSquare (unitPart x : ℚ_[p]) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  constructor
  · intro h
    obtain ⟨m, hm⟩ := even_valuation_of_isSquare hx h
    refine ⟨⟨m, hm⟩, ?_⟩
    have : x = (unitPart x : ℚ_[p]) * ((p : ℚ_[p]) ^ m) ^ 2 := by
      conv_lhs => rw [unitPart_spec x, hm, zpow_add₀ hp0]
      ring
    rwa [this, isSquare_mul_sq_iff (zpow_ne_zero _ hp0)] at h
  · rintro ⟨⟨m, hm⟩, h⟩
    have : x = (unitPart x : ℚ_[p]) * ((p : ℚ_[p]) ^ m) ^ 2 := by
      conv_lhs => rw [unitPart_spec x, hm, zpow_add₀ hp0]
      ring
    rw [this, isSquare_mul_sq_iff (zpow_ne_zero _ hp0)]
    exact h

theorem norm_lt_one_of_toZMod_eq_zero {z : ℤ_[p]} (h : toZMod z = 0) : ‖z‖ < 1 := by
  have : z ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← ker_toZMod, RingHom.mem_ker]; exact h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits] at this; exact this

/-- If `‖u‖ = ‖r‖² = 1` with `u = r²` in `ℚ_p`, then `r ∈ ℤ_p` and `u = r²` in `ℤ_p`. -/
theorem exists_padicInt_sq_of_isSquare {u : ℤ_[p]} (hu : ‖u‖ = 1) (h : IsSquare (u : ℚ_[p])) :
    ∃ r : ℤ_[p], ‖r‖ = 1 ∧ u = r * r := by
  obtain ⟨r, hr⟩ := h
  have hr1 : ‖r‖ = 1 := by
    have : ‖r‖ * ‖r‖ = 1 := by rw [← norm_mul, ← hr, ← PadicInt.norm_def, hu]
    nlinarith [norm_nonneg r]
  exact ⟨⟨r, hr1.le⟩, hr1, Subtype.ext hr⟩

/-- Lemma SQ(a): for odd `p`, a unit `u` of `ℤ_p` is a square in `ℚ_p` iff its residue is a square
mod `p`. -/
theorem isSquare_coe_iff_toZMod (hp2 : p ≠ 2) {u : ℤ_[p]} (hu : ‖u‖ = 1) :
    IsSquare (u : ℚ_[p]) ↔ IsSquare (toZMod u) := by
  constructor
  · intro h
    obtain ⟨r, -, rfl⟩ := exists_padicInt_sq_of_isSquare hu h
    exact ⟨toZMod r, map_mul _ _ _⟩
  · rintro ⟨s, hs⟩
    set a : ℤ_[p] := ((s.val : ℕ) : ℤ_[p])
    have ha : toZMod a = s := by simp [a]
    have hres : toZMod (u - a * a) = 0 := by rw [map_sub, map_mul, ha, hs, sub_self]
    have hs0 : s ≠ 0 := by
      rintro rfl
      have := norm_lt_one_of_toZMod_eq_zero (show toZMod u = 0 by rw [hs, mul_zero])
      rw [hu] at this; exact lt_irrefl _ this
    have ha1 : ‖a‖ = 1 := by
      refine le_antisymm (PadicInt.norm_le_one a) (not_lt.mp fun h => hs0 ?_)
      have : a ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
        (IsLocalRing.mem_maximalIdeal _).mpr (PadicInt.mem_nonunits.mpr h)
      rwa [← ker_toZMod, RingHom.mem_ker, ha] at this
    have ha0 : (a : ℚ_[p]) ≠ 0 := by
      intro h; rw [PadicInt.norm_def, h, norm_zero] at ha1; exact zero_ne_one ha1
    have hsq : IsSquare ((u : ℚ_[p]) / (a : ℚ_[p]) ^ 2) := by
      refine isSquare_of_norm_sub_one_lt ?_
      rw [padic_norm_two hp2, one_pow,
        show (u : ℚ_[p]) / (a : ℚ_[p]) ^ 2 - 1 = ((u - a * a : ℤ_[p]) : ℚ_[p]) / (a : ℚ_[p]) ^ 2 by
          push_cast; field_simp,
        norm_div, norm_pow, ← PadicInt.norm_def, ← PadicInt.norm_def, ha1, one_pow, div_one]
      exact norm_lt_one_of_toZMod_eq_zero hres
    rwa [isSquare_div_sq_iff ha0] at hsq

/-- Lemma SQ(b): a unit `u` of `ℤ₂` is a square in `ℚ₂` iff `u ≡ 1 (mod 8)`. -/
theorem isSquare_coe_iff_toZModPow_two {u : ℤ_[2]} (hu : ‖u‖ = 1) :
    IsSquare (u : ℚ_[2]) ↔ toZModPow 3 u = 1 := by
  constructor
  · intro h
    obtain ⟨r, hr1, rfl⟩ := exists_padicInt_sq_of_isSquare hu h
    obtain ⟨w, hw⟩ := (PadicInt.isUnit_iff.mpr hr1).exists_right_inv
    have hw' : toZModPow 3 r * toZModPow 3 w = 1 := by rw [← map_mul, hw, map_one]
    rw [map_mul]
    generalize toZModPow 3 r = z at hw'
    generalize toZModPow 3 w = z' at hw'
    revert z z'
    decide
  · intro h
    refine isSquare_of_norm_sub_one_lt ?_
    have h8 : ‖(1 : ℤ_[2]) - u‖ ≤ ((2 : ℕ) : ℝ) ^ (-(3 : ℕ) : ℤ) := by
      rw [norm_le_pow_iff_mem_span_pow, ← ker_toZModPow, RingHom.mem_ker, map_sub, map_one, h,
        sub_self]
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, norm_sub_rev] at h8
    rw [two_adic_norm_two]
    refine h8.trans_lt ?_
    norm_num

/-- **Lemma SQ** for odd `p`: a nonzero `x = p^v u` is a square in `ℚ_p` iff `v` is even and the
residue of the unit part `u` is a square mod `p`. -/
theorem isSquare_padic_iff (hp2 : p ≠ 2) {x : ℚ_[p]} (hx : x ≠ 0) :
    IsSquare x ↔ Even x.valuation ∧ IsSquare (toZMod (unitPart x)) := by
  rw [isSquare_iff_even_valuation hx, isSquare_coe_iff_toZMod hp2 (norm_unitPart hx)]

/-- **Lemma SQ** for `p = 2`: a nonzero `x = 2^v u` is a square in `ℚ₂` iff `v` is even and the
unit part satisfies `u ≡ 1 (mod 8)`. -/
theorem isSquare_two_adic_iff {x : ℚ_[2]} (hx : x ≠ 0) :
    IsSquare x ↔ Even x.valuation ∧ toZModPow 3 (unitPart x) = 1 := by
  rw [isSquare_iff_even_valuation hx, isSquare_coe_iff_toZModPow_two (norm_unitPart hx)]

/-! ### Rational tests -/

theorem padic_norm_intCast_eq_one {c : ℤ} (hc : ¬(p : ℤ) ∣ c) : ‖(c : ℚ_[p])‖ = 1 :=
  le_antisymm (Padic.norm_int_le_one c)
    (not_lt.mp fun h => hc (Padic.norm_intCast_lt_one_iff.mp h))

/-- **(RT)** for odd `p`, integer form: an integer prime to `p` that is a square mod `p` is a
square in `ℚ_p`. -/
theorem isSquare_intCast_of_residue (hp2 : p ≠ 2) {c : ℤ} (hc : ¬(p : ℤ) ∣ c)
    (h : IsSquare (c : ZMod p)) : IsSquare (c : ℚ_[p]) := by
  have hu : ‖(c : ℤ_[p])‖ = 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_intCast]; exact padic_norm_intCast_eq_one hc
  have := (isSquare_coe_iff_toZMod hp2 hu).mpr (by rwa [map_intCast])
  rwa [PadicInt.coe_intCast] at this

/-- **(RT)** for odd `p`: `m/n` with `p ∤ m n` and `m n` a square mod `p` is a square in `ℚ_p`. -/
theorem isSquare_intCast_div_of_residue (hp2 : p ≠ 2) {m n : ℤ} (hm : ¬(p : ℤ) ∣ m)
    (hn : ¬(p : ℤ) ∣ n) (h : IsSquare ((m * n : ℤ) : ZMod p)) :
    IsSquare ((m : ℚ_[p]) / n) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hn0 : (n : ℚ_[p]) ≠ 0 := by
    intro h0; apply hn; rw [Int.cast_eq_zero.mp h0]; exact dvd_zero _
  have hmn := isSquare_intCast_of_residue hp2 (fun h' => (hpZ.dvd_or_dvd h').elim hm hn) h
  rw [← isSquare_div_sq_iff hn0] at hmn
  rwa [show ((m * n : ℤ) : ℚ_[p]) / (n : ℚ_[p]) ^ 2 = (m : ℚ_[p]) / n by
    push_cast; field_simp] at hmn

/-- **(RT)** for odd `p`, rational form (nt-prop0 §2.1): a rational number whose numerator and
denominator are prime to `p`, and whose residue is a square mod `p`, is a square in `ℚ_p`. -/
theorem isSquare_ratCast_of_residue (hp2 : p ≠ 2) {q : ℚ} (hnum : ¬(p : ℤ) ∣ q.num)
    (hden : ¬p ∣ q.den) (h : IsSquare ((q.num * q.den : ℤ) : ZMod p)) :
    IsSquare (q : ℚ_[p]) := by
  have hden' : ¬(p : ℤ) ∣ (q.den : ℤ) := fun h' => hden (by exact_mod_cast h')
  have := isSquare_intCast_div_of_residue hp2 hnum hden' h
  rwa [show (q : ℚ_[p]) = (q.num : ℚ_[p]) / ((q.den : ℤ) : ℚ_[p]) by
    conv_lhs => rw [← Rat.num_div_den q]
    push_cast; rfl]

/-- **(RT)** for `p = 2`, integer form: `m/n` with `n` odd and `m ≡ n (mod 8)` is a square in
`ℚ₂`. -/
theorem isSquare_intCast_div_two_adic {m n : ℤ} (hn : Odd n) (h : m ≡ n [ZMOD 8]) :
    IsSquare ((m : ℚ_[2]) / n) := by
  have hn1 : ‖(n : ℚ_[2])‖ = 1 :=
    padic_norm_intCast_eq_one (by
      rw [Nat.cast_ofNat, ← even_iff_two_dvd, Int.not_even_iff_odd]; exact hn)
  have hn0 : (n : ℚ_[2]) ≠ 0 := by intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  obtain ⟨k, hk⟩ := (Int.ModEq.dvd h.symm)
  refine isSquare_of_norm_sub_one_lt ?_
  rw [show (m : ℚ_[2]) / n - 1 = ((m - n : ℤ) : ℚ_[2]) / n by push_cast; field_simp, norm_div,
    hn1, div_one, hk, two_adic_norm_two]
  push_cast
  rw [norm_mul, show (8 : ℚ_[2]) = 2 ^ 3 by norm_num, norm_pow, two_adic_norm_two]
  have := Padic.norm_int_le_one (p := 2) k
  nlinarith [norm_nonneg ((k : ℤ) : ℚ_[2])]

/-- **(RT)** for `p = 2`, rational form: a rational number with odd denominator whose numerator is
congruent to its denominator mod 8 (i.e. which is `≡ 1 (mod 8)` as a 2-adic unit) is a square
in `ℚ₂`. -/
theorem isSquare_ratCast_two_adic {q : ℚ} (hden : Odd q.den) (h : q.num ≡ q.den [ZMOD 8]) :
    IsSquare (q : ℚ_[2]) := by
  have := isSquare_intCast_div_two_adic (m := q.num) (n := q.den) (by exact_mod_cast hden) h
  rwa [show (q : ℚ_[2]) = (q.num : ℚ_[2]) / ((q.den : ℤ) : ℚ_[2]) by
    conv_lhs => rw [← Rat.num_div_den q]
    push_cast; rfl]

end ZInQ.RouteK.Selmer
