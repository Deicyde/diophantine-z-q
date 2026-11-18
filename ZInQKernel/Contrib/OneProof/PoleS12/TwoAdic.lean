import ZInQKernel.Contrib.PoleRC.LocalP
import ZInQKernel.RouteK.Selmer.Two

/-!
# The necessary condition at `2` (S12 L364–379)

ELLIOT (supplement S12, lines 364–379, inside `par:descent`): for `ℓ ≡ 3 (mod 4)`, a class in the
Kummer image of `E_ℓ(ℚ₂)` has both coordinates of even valuation; "no sufficiency is being
asserted". `locM_two_even` proves exactly this, following S12's case split on `v₂(x)`:

* `v(x) < 0`: the three factors have valuation `v(x)`;
* `v(x) > 0`: `x + 3ℓ`, `x − ℓ` are units;
* `v(x) = 0`, `v(x − ℓ) = 1`: `(y/2)² = (ℓ + 2u)u(u + 2ℓ) ≡ ℓ (mod 8)` with `ℓ ≡ 3, 7 (mod 8)`,
  impossible (`no_mod_eight`);
* `v(x) = 0`, `v(x − ℓ) ≥ 2`: one of `x − ℓ`, `x + 3ℓ` has valuation exactly `2` (their difference
  is `4ℓ`), and the valuation sum is even.

`two_adic_odd`: for squarefree integers this says `a` and `b` are odd.
-/

namespace ZInQ.Manuscript.PoleS12

open ZInQ.RouteK.Selmer ZInQ.Manuscript.PoleRC PadicInt

theorem val_eq_of_norm_eq {u w : ℚ_[2]} (hu : u ≠ 0) (hw : w ≠ 0) (h : ‖u‖ = ‖w‖) :
    u.valuation = w.valuation := by
  rw [two_adic_norm_eq_zpow hu, two_adic_norm_eq_zpow hw] at h
  have := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) h
  simpa using this

theorem ne_zero_of_norm_pos {u : ℚ_[2]} {r : ℝ} (hr : 0 < r) (h : ‖u‖ = r) : u ≠ 0 := by
  rintro rfl; rw [norm_zero] at h; linarith

theorem val_of_norm_one {u : ℚ_[2]} (hu : ‖u‖ = 1) : u.valuation = 0 := by
  have := val_eq_of_norm_eq (ne_zero_of_norm_pos one_pos hu) one_ne_zero (by rw [hu, norm_one])
  rwa [Padic.valuation_one] at this

theorem val_of_norm_quarter {u : ℚ_[2]} (hu : ‖u‖ = 1 / 4) : u.valuation = 2 := by
  have h4 : (4 : ℚ_[2]) ≠ 0 := by norm_num
  have := val_eq_of_norm_eq (ne_zero_of_norm_pos (by norm_num) hu) h4
    (by rw [hu, two_adic_norm_four])
  rw [this, show (4 : ℚ_[2]) = (2 : ℚ_[2]) ^ 2 by norm_num, Padic.valuation_pow]
  have : (2 : ℚ_[2]).valuation = 1 := by
    have := Padic.valuation_p (p := 2); exact_mod_cast this
  rw [this]; rfl

theorem even_iff_of_sqEq {A B : ℚ_[2]} (hB : B ≠ 0) (h : SqEq A B) :
    Even A.valuation ↔ Even B.valuation := by
  obtain ⟨s, hs, rfl⟩ := h
  rw [Padic.valuation_mul hB (pow_ne_zero 2 hs), Padic.valuation_pow, Int.even_add]
  simp only [Nat.cast_ofNat, even_two, Even.mul_right, iff_true]

theorem norm_add_of_lt {x y : ℚ_[2]} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [Padic.add_eq_max_of_ne h.ne', max_eq_left h.le]

/-- **The `mod 8` step** (S12 L370–374): over `ℤ/8`, `u(ℓ + 2u)(u + 2ℓ) ≡ ℓu² ≡ ℓ` for odd `u`,
and `ℓ ≡ 3, 7` is not `1`. -/
theorem no_mod_eight : ∀ u w l : ZMod (2 ^ 3), u * w = 1 → (l = 3 ∨ l = 7) →
    u * (l + 2 * u) * (u + 2 * l) ≠ 1 := by decide

theorem no_mod_eight_case {ℓ : ℕ} (hℓ : ℓ % 4 = 3) {x : ℚ_[2]} (hx : ‖x‖ = 1)
    (hxl : ‖x - ℓ‖ = 1 / 2) (hP : IsSquare (x * (x - ℓ) * (x + 3 * ℓ))) : False := by
  have hL : ‖(ℓ : ℚ_[2])‖ = 1 := two_adic_norm_natCast_of_odd (by rw [Nat.odd_iff]; omega)
  set u : ℚ_[2] := (x - ℓ) / 2 with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_div, hxl, two_adic_norm_two]; norm_num
  have hxu : x = ℓ + 2 * u := by rw [hu_def]; ring
  have h2u : ‖2 * u‖ = 1 / 2 := by rw [norm_mul, two_adic_norm_two, hu, mul_one]
  have h2L : ‖2 * (ℓ : ℚ_[2])‖ = 1 / 2 := by rw [norm_mul, two_adic_norm_two, hL, mul_one]
  have hW : x * (x - ℓ) * (x + 3 * ℓ) = 4 * (u * (ℓ + 2 * u) * (u + 2 * ℓ)) := by
    rw [hxu]; ring
  have hWsq : IsSquare (u * (ℓ + 2 * u) * (u + 2 * ℓ)) := by
    rw [hW] at hP
    obtain ⟨r, hr⟩ := hP
    exact ⟨r / 2, by field_simp; linear_combination hr⟩
  -- lift to `ℤ₂`
  set U : ℤ_[2] := ⟨u, hu.le⟩
  set LZ : ℤ_[2] := (ℓ : ℤ_[2])
  set WZ : ℤ_[2] := U * (LZ + 2 * U) * (U + 2 * LZ)
  have hWZ : (WZ : ℚ_[2]) = u * (ℓ + 2 * u) * (u + 2 * ℓ) := by
    simp only [WZ, U, LZ, PadicInt.coe_mul, PadicInt.coe_add, PadicInt.coe_natCast]
    push_cast; rfl
  have hn1 : ‖(ℓ : ℚ_[2]) + 2 * u‖ = 1 := by
    rw [norm_add_of_lt (by rw [h2u, hL]; norm_num), hL]
  have hn2 : ‖u + 2 * (ℓ : ℚ_[2])‖ = 1 := by
    rw [norm_add_of_lt (by rw [h2L, hu]; norm_num), hu]
  have hWn : ‖WZ‖ = 1 := by
    rw [PadicInt.norm_def, hWZ, norm_mul, norm_mul, hu, hn1, hn2]; norm_num
  have h8 := (isSquare_coe_iff_toZModPow_two hWn).mp (by rw [hWZ]; exact hWsq)
  obtain ⟨w, hw⟩ := (PadicInt.isUnit_iff.mpr (show ‖U‖ = 1 from hu)).exists_right_inv
  have hw' : toZModPow 3 U * toZModPow 3 w = 1 := by rw [← map_mul, hw, map_one]
  have hl : toZModPow 3 LZ = 3 ∨ toZModPow 3 LZ = 7 := by
    simp only [LZ, map_natCast]
    rw [← ZMod.natCast_mod ℓ (2 ^ 3)]
    have : ℓ % 2 ^ 3 = 3 ∨ ℓ % 2 ^ 3 = 7 := by omega
    rcases this with h | h <;> rw [h]
    · left; rfl
    · right; rfl
  simp only [WZ, map_mul, map_add, map_ofNat] at h8
  exact no_mod_eight _ _ _ hw' hl h8

/-- **The necessary condition at `2`** (S12 L364–379, ELLIOT (supplement)): for `ℓ ≡ 3 (mod 4)`,
both coordinates of a class in the Kummer image of `E_ℓ(ℚ₂)` have even valuation. -/
theorem locM_two_even {ℓ : ℕ} (hℓ : ℓ % 4 = 3) {A B : ℚ_[2]} (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (h : LocM ℚ_[2] ℓ A B) : Even A.valuation ∧ Even B.valuation := by
  have hL : ‖(ℓ : ℚ_[2])‖ = 1 := two_adic_norm_natCast_of_odd (by rw [Nat.odd_iff]; omega)
  have hL0 : (ℓ : ℚ_[2]) ≠ 0 := ne_zero_of_norm_pos one_pos hL
  have h3 : ‖(3 : ℚ_[2])‖ = 1 := by
    have := two_adic_norm_intCast_of_odd (c := 3) ⟨1, rfl⟩; simpa using this
  have hnL : ‖-(ℓ : ℚ_[2])‖ = 1 := by rw [norm_neg, hL]
  have h3L : ‖3 * (ℓ : ℚ_[2])‖ = 1 := by rw [norm_mul, h3, hL, one_mul]
  have hm3L : ‖-3 * (ℓ : ℚ_[2])‖ = 1 := by rw [norm_mul, norm_neg, h3, hL, one_mul]
  have h4L : ‖4 * (ℓ : ℚ_[2])‖ = 1 / 4 := by rw [norm_mul, two_adic_norm_four, hL, mul_one]
  have hAB : (A * B).valuation = A.valuation + B.valuation := Padic.valuation_mul hA0 hB0
  have hu : ∀ {Z u : ℚ_[2]}, ‖u‖ = 1 → SqEq Z u → Even Z.valuation :=
    fun hu h => even_valuation_of_sqEq_unit hu h
  rcases h with ⟨hsa, hsb⟩ | ⟨x, h₁, h₂, h₃⟩
  · exact ⟨even_valuation_of_isSquare hA0 hsa, even_valuation_of_isSquare hB0 hsb⟩
  rcases locM_torsion hL0 hA0 hB0 h₁ h₂ h₃ with ⟨-, hb', hab'⟩ | ⟨-, ha', hab'⟩ | ⟨-, ha', hb'⟩ |
    ⟨hx0, hxb, hxa, hxa', hxb', hxab⟩
  · have e1 := hu hnL hb'
    have e2 := hu hm3L hab'
    rw [hAB, Int.even_add] at e2
    exact ⟨e2.mpr e1, e1⟩
  · have e1 := hu hL ha'
    have e2 := hu hL hab'
    rw [hAB, Int.even_add] at e2
    exact ⟨e1, e2.mp e1⟩
  · exact ⟨hu h3L ha', hu hnL hb'⟩
  have eA := (even_iff_of_sqEq hA0 hxa').symm
  have eB := (even_iff_of_sqEq hB0 hxb').symm
  have eAB := (even_iff_of_sqEq (mul_ne_zero hA0 hB0) hxab).symm
  rw [hAB, Int.even_add] at eAB
  rcases lt_trichotomy ‖x‖ 1 with hlt | heq | hgt
  · have n1 : ‖x + 3 * (ℓ : ℚ_[2])‖ = 1 := by
      rw [add_comm, norm_add_of_lt (by rwa [h3L]), h3L]
    have n2 : ‖x - (ℓ : ℚ_[2])‖ = 1 := by
      rw [sub_eq_add_neg, add_comm, norm_add_of_lt (by rwa [hnL]), hnL]
    rw [val_of_norm_one n1] at eA
    rw [val_of_norm_one n2] at eB
    exact ⟨eA.mpr ⟨0, rfl⟩, eB.mpr ⟨0, rfl⟩⟩
  · rw [val_of_norm_one heq] at eAB
    have eAB' : Even A.valuation ↔ Even B.valuation := eAB.mpr ⟨0, rfl⟩
    have hlt1 : ‖x - (ℓ : ℚ_[2])‖ < 1 := by
      rw [sub_eq_add_neg]
      have := two_adic_norm_add_lt (u := x) (w := -(ℓ : ℚ_[2])) (neg_ne_zero.mpr hL0)
        (by rw [heq, hnL])
      rwa [hnL] at this
    have hle : ‖x - (ℓ : ℚ_[2])‖ ≤ 1 / 2 := by
      have := two_adic_norm_le_of_lt (k := 0) (by simpa using hlt1)
      simpa using this
    by_cases hh : ‖x - (ℓ : ℚ_[2])‖ = 1 / 2
    · exfalso
      refine no_mod_eight_case hℓ heq hh ?_
      have := (hxab.mul hxb').mul hxa'
      have hsq := this.isSquare_mul
      rw [show x * (x - ℓ) * (x + 3 * ℓ) * (A * B * B * A) =
        (x * (x - ℓ) * (x + 3 * ℓ)) * (A * B) ^ 2 by ring] at hsq
      obtain ⟨r, hr⟩ := hsq
      refine ⟨r / (A * B), ?_⟩
      have hAB0 : A * B ≠ 0 := mul_ne_zero hA0 hB0
      field_simp
      linear_combination hr
    · have hlt2 : ‖x - (ℓ : ℚ_[2])‖ < 1 / 2 := lt_of_le_of_ne hle hh
      have hle4 : ‖x - (ℓ : ℚ_[2])‖ ≤ 1 / 4 := by
        have := two_adic_norm_le_of_lt (k := -1) (by
          rw [show (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 by norm_num]; exact hlt2)
        rw [show (2 : ℝ) ^ (-1 - 1 : ℤ) = 1 / 4 by norm_num] at this
        exact this
      by_cases h4 : ‖x - (ℓ : ℚ_[2])‖ = 1 / 4
      · rw [val_of_norm_quarter h4] at eB
        have hb := eB.mpr ⟨1, rfl⟩
        exact ⟨eAB'.mpr hb, hb⟩
      · have hlt4 : ‖x - (ℓ : ℚ_[2])‖ < 1 / 4 := lt_of_le_of_ne hle4 h4
        have n1 : ‖x + 3 * (ℓ : ℚ_[2])‖ = 1 / 4 := by
          rw [show x + 3 * (ℓ : ℚ_[2]) = 4 * ℓ + (x - ℓ) by ring,
            norm_add_of_lt (by rwa [h4L]), h4L]
        rw [val_of_norm_quarter n1] at eA
        have ha := eA.mpr ⟨1, rfl⟩
        exact ⟨ha, eAB'.mp ha⟩
  · have n1 : ‖x + 3 * (ℓ : ℚ_[2])‖ = ‖x‖ := norm_add_of_lt (by rwa [h3L])
    have n2 : ‖x - (ℓ : ℚ_[2])‖ = ‖x‖ := by
      rw [sub_eq_add_neg]; exact norm_add_of_lt (by rwa [hnL])
    rw [val_eq_of_norm_eq hxa hx0 n1] at eA
    rw [val_eq_of_norm_eq hxb hx0 n2] at eB
    rw [eA, eB] at eAB
    have hx : Even x.valuation := eAB.mp Iff.rfl
    exact ⟨eA.mpr hx, eB.mpr hx⟩

/-- **`a` and `b` are odd** for a class `(a, b)` of squarefree integers in the Kummer image of
`E_ℓ(ℚ₂)`, `ℓ ≡ 3 (mod 4)` (S12 L364–379). -/
theorem two_adic_odd {ℓ : ℕ} (hℓ : ℓ % 4 = 3) {a b : ℤ} (ha : Squarefree a) (hb : Squarefree b)
    (h : LocM ℚ_[2] ℓ a b) : a % 2 = 1 ∧ b % 2 = 1 := by
  have hA0 : (a : ℚ_[2]) ≠ 0 := Int.cast_ne_zero.mpr ha.ne_zero
  have hB0 : (b : ℚ_[2]) ≠ 0 := Int.cast_ne_zero.mpr hb.ne_zero
  obtain ⟨eA, eB⟩ := locM_two_even hℓ hA0 hB0 h
  rw [Padic.valuation_intCast] at eA eB
  have h1 := not_dvd_of_squarefree_of_even_padicValInt ha (Int.even_coe_nat _ |>.mp eA)
  have h2 := not_dvd_of_squarefree_of_even_padicValInt hb (Int.even_coe_nat _ |>.mp eB)
  push_cast at h1 h2
  omega

end ZInQ.Manuscript.PoleS12
