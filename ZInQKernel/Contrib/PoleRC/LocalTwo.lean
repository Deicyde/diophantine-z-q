import ZInQKernel.Contrib.PoleRC.LocalThreeBad
import ZInQKernel.RouteK.Selmer.Bits

/-!
# The local image at `2`: `LocalTwo`

For squarefree `ℓ ≡ 3 (mod 4)` and squarefree `a, b`:
`LocM ℚ₂ ℓ a b ↔ a odd ∧ b ≡ 1 (mod 4)` (the Prop `LocalTwo` of `Count.lean`), proved here.

FIDELITY. S12 (`parity-frozen-4eaee875.tex`) lines 359–374 assert only the necessary condition
that both Kummer coordinates have even valuation at `2` ("no sufficiency is being asserted",
line 374), and at `2` the descent needs sufficiency only for the class `(β, 1)`, which is the
identity class there (S12 lines 442–443). The Prop `LocalTwo` of the branch is stronger than S12
in both directions (MISMATCH, reported): it adds `b ≡ 1 (mod 4)` to the necessity and asserts the
full sufficiency. Both are true and proved here.

* "only if" (`locM_two_nec_classes`): the case split of S12 lines 361–372 on the witness `x`
  (`v₂(x) < 0` even; `x` even; `x` odd with `x − ℓ = 2u` impossible because the square
  `(y/2)²` would be `≡ ℓ (mod 8)`; otherwise `v₂(x − ℓ), v₂(x + 3ℓ) ≥ 2` with difference `4ℓ`).
  Refinement beyond S12 (DEPARTURE): in each case the classes of `a` and `b` are identified, which
  gives `b ≡ 1 (mod 4)`. The model is Route K's `Selmer/Two.lean`.
* "if" (`locM_two_suff`): the four torsion classes (S12 lines 318–324) and the four classes
  `τ·(5, 5)`, with the rational witnesses `x = 1/4`, `ℓ + 80ℓ²`, `−3ℓ + 112ℓ²`, `20ℓ²`
  (DEPARTURE: not in S12, which asserts no sufficiency at `2`). The image has the eight classes
  `(ℓ^i 3^j 5^k, (−ℓ)^j 5^k)`.
-/

namespace ZInQ.Manuscript.PoleRC

open ZInQ.RouteK.Selmer

/-- `u = v s²`, `s ≠ 0`, gives `u ≡ v`. -/
theorem sqEq_of_eq_mul_sq {K : Type*} [Field K] {u v s : K} (hs : s ≠ 0) (h : u = v * s ^ 2) :
    SqEq u v := ⟨s, hs, h⟩

/-- `x + y ≡ 5x` when `‖y‖ = ‖x‖/4` in `ℚ₂`. -/
theorem sqEq_add_five_two_adic {x y : ℚ_[2]} (hx : x ≠ 0) (h : ‖y‖ = ‖x‖ / 4) :
    SqEq (x + y) (5 * x) := by
  have h4 : (4 : ℚ_[2]) * x ≠ 0 := mul_ne_zero (by norm_num) hx
  have hy : ‖y‖ = ‖-(4 * x)‖ := by rw [norm_neg, norm_mul, two_adic_norm_four, h]; ring
  have := two_adic_norm_add_lt (neg_ne_zero.mpr h4) hy
  rw [norm_neg, norm_mul, two_adic_norm_four] at this
  rw [show x + y = 5 * x + (y + -(4 * x)) by ring]
  refine sqEq_add_two_adic ?_
  rw [norm_mul, two_adic_norm_five]
  linarith

/-- **The classes at `2`, "only if"** (S12 lines 359–374, refined). -/
theorem locM_two_nec_classes {L A B : ℚ_[2]} (hL : ‖L‖ = 1) (hLns : ¬ IsSquare L)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (h : LocM ℚ_[2] L A B) :
    (∃ i j k : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧ SqEq A (L ^ i * 3 ^ j * 5 ^ k)) ∧
      ∃ j k : ℕ, j < 2 ∧ k < 2 ∧ SqEq B ((-L) ^ j * 5 ^ k) := by
  have hL0 : L ≠ 0 := by intro h0; rw [h0, norm_zero] at hL; exact zero_ne_one hL
  have hn3 : ‖(3 : ℚ_[2])‖ = 1 := by
    have := two_adic_norm_intCast_of_odd (c := 3) ⟨1, rfl⟩; simpa using this
  have hn3L : ‖3 * L‖ = 1 := by rw [norm_mul, hn3, hL, one_mul]
  have hn4L : ‖4 * L‖ = 1 / 4 := by rw [norm_mul, two_adic_norm_four, hL, mul_one]
  have hn5 := two_adic_norm_five
  have h3L0 : 3 * L ≠ 0 := mul_ne_zero (by norm_num) hL0
  have h4L0 : 4 * L ≠ 0 := mul_ne_zero (by norm_num) hL0
  have key : ∀ i j k j' k' : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧ j' < 2 ∧ k' < 2 →
      SqEq A (L ^ i * 3 ^ j * 5 ^ k) → SqEq B ((-L) ^ j' * 5 ^ k') →
      (∃ i j k : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧ SqEq A (L ^ i * 3 ^ j * 5 ^ k)) ∧
        ∃ j k : ℕ, j < 2 ∧ k < 2 ∧ SqEq B ((-L) ^ j * 5 ^ k) :=
    fun i j k j' k' hb h1 h2 => ⟨⟨i, j, k, hb.1, hb.2.1, hb.2.2.1, h1⟩, j', k', hb.2.2.2.1,
      hb.2.2.2.2, h2⟩
  rcases h with ⟨hsa, hsb⟩ | ⟨x, h₁, h₂, h₃⟩
  · exact key 0 0 0 0 0 (by norm_num) ((sqEq_one_of_isSquare hA0 hsa).trans_eq (by ring))
      ((sqEq_one_of_isSquare hB0 hsb).trans_eq (by ring))
  rcases locM_torsion hL0 hA0 hB0 h₁ h₂ h₃ with ⟨-, hb', hab'⟩ | ⟨-, ha', hab'⟩ | ⟨-, ha', hb'⟩ |
    ⟨hx0, hxb, hxa, hxa', hxb', hxab⟩
  · have ha' : SqEq A (-3 * L * -L) := sqEq_of_mul_sqEq hab' hb' (neg_ne_zero.mpr hL0)
    exact key 0 1 0 1 0 (by norm_num)
      ((ha'.trans (sqEq_of_eq_mul_sq (v := 3) hL0 (by ring))).trans_eq (by ring))
      (hb'.trans_eq (by ring))
  · have hba : SqEq (B * A) L := by rw [mul_comm]; exact hab'
    exact key 1 0 0 0 0 (by norm_num) (ha'.trans_eq (by ring))
      (((sqEq_of_mul_sqEq hba ha' hL0).trans (sqEq_of_eq_mul_sq (v := 1) hL0 (by ring))).trans_eq
        (by ring))
  · exact key 1 1 0 1 0 (by norm_num) (ha'.trans_eq (by ring)) (hb'.trans_eq (by ring))
  -- the generic case: `x(x − ℓ)(x + 3ℓ)` is a nonzero square
  have hz0 : x * (x - L) * (x + 3 * L) ≠ 0 := mul_ne_zero (mul_ne_zero hx0 hxb) hxa
  have hprod : SqEq (x * (x - L) * (x + 3 * L)) 1 := by
    have := (hxab.mul hxb').mul hxa'
    exact this.trans ⟨A * B, mul_ne_zero hA0 hB0, by ring⟩
  have hsq : IsSquare (x * (x - L) * (x + 3 * L)) := by
    obtain ⟨s, -, hs⟩ := hprod; exact ⟨s, by rw [hs]; ring⟩
  have hodd := padic_norm_ne_zpow_odd hz0 hsq
  have hznorm : ‖x * (x - L) * (x + 3 * L)‖ = ‖x‖ * ‖x - L‖ * ‖x + 3 * L‖ := by
    rw [norm_mul, norm_mul]
  have disc : ∀ (z : ℚ_[2]) (k : ℤ) (r : ℝ), ‖z‖ < (2 : ℝ) ^ k → (2 : ℝ) ^ (k - 1) = r →
      ‖z‖ ≤ r := fun z k r h e => e ▸ two_adic_norm_le_of_lt h
  have hxn := two_adic_norm_eq_zpow hx0
  set v := x.valuation with hv_def
  rcases (by omega : v ≤ -3 ∨ v = -2 ∨ v = -1 ∨ v = 0 ∨ v = 1 ∨ 2 ≤ v) with
    hv | hv | hv | hv | hv | hv
  · -- `v ≤ −3`: `x − ℓ ≡ x + 3ℓ ≡ x ≡ 1` (S12 line 361)
    have h8 : (8 : ℝ) ≤ ‖x‖ := by
      rw [hxn]
      calc (8 : ℝ) = 2 ^ (3 : ℤ) := by norm_num
        _ ≤ 2 ^ (-v) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have e₂ : SqEq (x - L) x := by
      rw [sub_eq_add_neg]
      exact sqEq_add_of_norm_le_two_adic (by rw [norm_neg, hL]; linarith)
    have e₃ : SqEq (x + 3 * L) x := sqEq_add_of_norm_le_two_adic (by rw [hn3L]; linarith)
    have hb' : SqEq B x := hxb'.symm.trans e₂
    have ha' : SqEq A x := hxa'.symm.trans e₃
    have hab : SqEq (A * B) x := hxab.symm
    have hb1 : SqEq B 1 :=
      ((sqEq_of_mul_sqEq (by rw [mul_comm]; exact hab) ha' hx0).trans_eq (by ring) :
        SqEq B (1 * x ^ 2)).of_mul_sq hx0
    exact key 0 0 0 0 0 (by norm_num) ((ha'.trans (hb'.symm.trans hb1)).trans_eq (by ring))
      (hb1.trans_eq (by ring))
  · -- `v = −2`: `x − ℓ ≡ x + 3ℓ ≡ 5x`, `x ≡ 1`: the class `(5, 5)`
    have h4 : ‖x‖ = 4 := by rw [hxn, hv]; norm_num
    have h4x : ‖4 * x‖ = 1 := by rw [norm_mul, two_adic_norm_four, h4]; norm_num
    have l₁ := two_adic_norm_add_lt hL0 (h4x.trans hL.symm)
    have l₂ := two_adic_norm_add_lt h3L0 ((norm_neg (4 * x)).trans (h4x.trans hn3L.symm))
    have e₂ : SqEq (x - L) (5 * x) := by
      rw [show x - L = 5 * x + -(4 * x + L) by ring]
      refine sqEq_add_two_adic ?_
      rw [norm_neg, norm_mul, hn5, h4]; linarith
    have e₃ : SqEq (x + 3 * L) (5 * x) := by
      rw [show x + 3 * L = 5 * x + (-(4 * x) + 3 * L) by ring]
      refine sqEq_add_two_adic ?_
      rw [norm_mul, hn5, h4]; linarith
    have h5x : 5 * x ≠ 0 := mul_ne_zero (by norm_num) hx0
    have ex : SqEq x 1 := by
      have := (((SqEq.refl x).mul e₂).mul e₃).symm.trans hprod
      exact ((this.symm.trans_eq (by ring) : SqEq 1 (x * (5 * x) ^ 2)).of_mul_sq h5x).symm
    exact key 0 0 1 0 1 (by norm_num)
      ((hxa'.symm.trans (e₃.trans ((SqEq.refl 5).mul ex))).trans_eq (by ring))
      ((hxb'.symm.trans (e₂.trans ((SqEq.refl 5).mul ex))).trans_eq (by ring))
  · -- `v = −1`: `‖x(x − ℓ)(x + 3ℓ)‖ = 8` (S12 line 361)
    exfalso
    have h2x : ‖x‖ = 2 := by rw [hxn, hv]; norm_num
    have n₂ : ‖x - L‖ = 2 := by
      rw [sub_eq_add_neg, Padic.add_eq_max_of_ne (by rw [norm_neg, hL, h2x]; norm_num),
        norm_neg, hL, h2x]; norm_num
    have n₃ : ‖x + 3 * L‖ = 2 := by
      rw [Padic.add_eq_max_of_ne (by rw [hn3L, h2x]; norm_num), hn3L, h2x]; norm_num
    apply hodd 1
    rw [hznorm, h2x, n₂, n₃]; norm_num
  · -- `v = 0`: `x` odd (S12 lines 362–372)
    have h1x : ‖x‖ = 1 := by rw [hxn, hv]; norm_num
    have hP : ‖x - L‖ < 1 := by
      have := two_adic_norm_add_lt (neg_ne_zero.mpr hL0) (by rw [norm_neg, hL, h1x] : ‖x‖ = ‖-L‖)
      rwa [← sub_eq_add_neg, norm_neg, hL] at this
    have hP2 : ‖x - L‖ ≤ 1 / 2 := disc _ 0 _ (by simpa using hP) (by norm_num)
    by_cases hPh : ‖x - L‖ = 1 / 2
    · -- `x − ℓ = 2u`: `x(x − ℓ)(x + 3ℓ) ≡ ℓ`, not a square (S12 lines 363–368)
      exfalso
      set u := (x - L) / 2 with hu
      have hu1 : ‖u‖ = 1 := by rw [hu, norm_div, hPh, two_adic_norm_two]; norm_num
      have hu0 : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hu1; exact zero_ne_one hu1
      set r := u / L with hr
      have hr1 : ‖r‖ = 1 := by rw [hr, norm_div, hu1, hL]; norm_num
      have hr0 : r ≠ 0 := by intro h0; rw [h0, norm_zero] at hr1; exact zero_ne_one hr1
      have hr2 : ‖r + 1‖ ≤ 1 / 2 :=
        disc _ 0 _ (by have := two_adic_norm_one_add_lt hr1; rw [add_comm]; simpa using this)
          (by norm_num)
      have hxu : x = L + 2 * u := by rw [hu]; ring
      have hid : x * (x - L) * (x + 3 * L) = L * (1 + 2 * (r + 1) ^ 2 / r) * (2 * u) ^ 2 := by
        rw [hxu, hr]; field_simp; ring
      have hw : ‖2 * (r + 1) ^ 2 / r‖ ≤ ‖(1 : ℚ_[2])‖ / 8 := by
        rw [norm_div, norm_mul, norm_pow, two_adic_norm_two, hr1, norm_one]
        have h0 : 0 ≤ ‖r + 1‖ := norm_nonneg _
        nlinarith
      have e1 : SqEq (1 + 2 * (r + 1) ^ 2 / r) 1 := sqEq_add_of_norm_le_two_adic hw
      have hfL : SqEq (x * (x - L) * (x + 3 * L)) L := by
        rw [hid]
        exact (sqEq_of_eq_mul_sq (v := L * (1 + 2 * (r + 1) ^ 2 / r))
          (mul_ne_zero two_ne_zero hu0) rfl).trans (((SqEq.refl L).mul e1).trans_eq (by ring))
      apply hLns
      obtain ⟨s, -, hs⟩ := hfL.symm.trans hprod
      exact ⟨s, by rw [hs]; ring⟩
    have hP4 : ‖x - L‖ ≤ 1 / 4 :=
      disc _ (-1) _ (by norm_num; exact lt_of_le_of_ne hP2 hPh) (by norm_num)
    have hdiff : (x + 3 * L) + -(x - L) = 4 * L := by ring
    by_cases hP4e : ‖x - L‖ = 1 / 4
    · -- `v₂(x − ℓ) = 2`, `v₂(x + 3ℓ) ≥ 4`: `x ≡ −3ℓ`, `b ≡ −ℓ` or `−5ℓ`
      have hQ4 : ‖x + 3 * L‖ < 1 / 4 := by
        refine lt_of_le_of_ne ?_ fun hQe => ?_
        · rw [show x + 3 * L = (x - L) + 4 * L by ring]
          exact (Padic.nonarchimedean _ _).trans (by rw [hP4e, hn4L, max_self])
        · have := two_adic_norm_add_lt (u := x + 3 * L) (w := -(x - L)) (neg_ne_zero.mpr hxb)
            (by rw [norm_neg, hQe, hP4e])
          rw [hdiff, hn4L, norm_neg, hP4e] at this; exact lt_irrefl _ this
      have hQ8 : ‖x + 3 * L‖ ≤ 1 / 8 := disc _ (-2) _ (by norm_num; linarith) (by norm_num)
      have hQ16 : ‖x + 3 * L‖ ≤ 1 / 16 := by
        refine disc _ (-3) _ (lt_of_le_of_ne (by norm_num; linarith) fun he => hodd (-3) ?_)
          (by norm_num)
        rw [hznorm, h1x, hP4e, he]; norm_num
      have ex : SqEq x (-(3 * L)) := by
        have := sqEq_add_of_norm_le_two_adic (x := -(3 * L)) (y := x + 3 * L)
          (by rw [norm_neg, hn3L]; linarith)
        rwa [show -(3 * L) + (x + 3 * L) = x by ring] at this
      have hB' : SqEq (x - L) (-(4 * L)) ∨ SqEq (x - L) (5 * -(4 * L)) := by
        have := sqEq_add_or_five_two_adic (x := -(4 * L)) (y := x + 3 * L)
          (neg_ne_zero.mpr h4L0) (by rw [norm_neg, hn4L]; linarith)
        rwa [show -(4 * L) + (x + 3 * L) = x - L by ring] at this
      have hab : SqEq (A * B) (-(3 * L)) := hxab.symm.trans ex
      rcases hB' with hB' | hB'
      · have hb' : SqEq B (-L) :=
          (hxb'.symm.trans hB').trans (sqEq_of_eq_mul_sq (v := -L) two_ne_zero (by ring))
        have ha' := sqEq_of_mul_sqEq hab hb' (neg_ne_zero.mpr hL0)
        exact key 0 1 0 1 0 (by norm_num)
          ((ha'.trans (sqEq_of_eq_mul_sq (v := 3) hL0 (by ring))).trans_eq (by ring))
          (hb'.trans_eq (by ring))
      · have hb' : SqEq B (-(5 * L)) :=
          (hxb'.symm.trans hB').trans (sqEq_of_eq_mul_sq (v := -(5 * L)) two_ne_zero (by ring))
        have ha' := sqEq_of_mul_sqEq hab hb' (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hL0))
        exact key 0 1 1 1 1 (by norm_num)
          ((ha'.trans (sqEq_of_eq_mul_sq (v := 15) hL0 (by ring))).trans_eq (by ring))
          (hb'.trans_eq (by ring))
    · -- `v₂(x + 3ℓ) = 2`, `v₂(x − ℓ) ≥ 4`: `x ≡ ℓ`, `a ≡ ℓ` or `5ℓ`
      have hPl : ‖x - L‖ < 1 / 4 := lt_of_le_of_ne hP4 hP4e
      have hQe : ‖x + 3 * L‖ = 1 / 4 := by
        rw [show x + 3 * L = 4 * L + (x - L) by ring,
          Padic.add_eq_max_of_ne (by rw [hn4L]; exact (ne_of_lt hPl).symm), hn4L]
        exact max_eq_left hPl.le
      have hP8 : ‖x - L‖ ≤ 1 / 8 := disc _ (-2) _ (by norm_num; linarith) (by norm_num)
      have hP16 : ‖x - L‖ ≤ 1 / 16 := by
        refine disc _ (-3) _ (lt_of_le_of_ne (by norm_num; linarith) fun he => hodd (-3) ?_)
          (by norm_num)
        rw [hznorm, h1x, hQe, he]; norm_num
      have ex : SqEq x L := by
        have := sqEq_add_of_norm_le_two_adic (x := L) (y := x - L) (by rw [hL]; linarith)
        rwa [show L + (x - L) = x by ring] at this
      have hA' : SqEq (x + 3 * L) (4 * L) ∨ SqEq (x + 3 * L) (5 * (4 * L)) := by
        have := sqEq_add_or_five_two_adic (x := 4 * L) (y := x - L) h4L0
          (by rw [hn4L]; linarith)
        rwa [show 4 * L + (x - L) = x + 3 * L by ring] at this
      have hba : SqEq (B * A) L := by rw [mul_comm]; exact hxab.symm.trans ex
      rcases hA' with hA' | hA'
      · have ha' : SqEq A L :=
          (hxa'.symm.trans hA').trans (sqEq_of_eq_mul_sq (v := L) two_ne_zero (by ring))
        have hb' := sqEq_of_mul_sqEq hba ha' hL0
        exact key 1 0 0 0 0 (by norm_num) (ha'.trans_eq (by ring))
          ((hb'.trans (sqEq_of_eq_mul_sq (v := 1) hL0 (by ring))).trans_eq (by ring))
      · have ha' : SqEq A (5 * L) :=
          (hxa'.symm.trans hA').trans (sqEq_of_eq_mul_sq (v := 5 * L) two_ne_zero (by ring))
        have hb' := sqEq_of_mul_sqEq hba ha' (mul_ne_zero (by norm_num) hL0)
        exact key 1 0 1 0 1 (by norm_num) (ha'.trans_eq (by ring))
          ((hb'.trans (sqEq_of_eq_mul_sq (v := 5) hL0 (by ring))).trans_eq (by ring))
  · -- `v = 1`: `‖x(x − ℓ)(x + 3ℓ)‖ = 1/2`
    exfalso
    have h2x : ‖x‖ = 1 / 2 := by rw [hxn, hv]; norm_num
    have n₂ : ‖x - L‖ = 1 := by
      rw [sub_eq_add_neg, Padic.add_eq_max_of_ne (by rw [norm_neg, hL, h2x]; norm_num),
        norm_neg, hL, h2x]; norm_num
    have n₃ : ‖x + 3 * L‖ = 1 := by
      rw [Padic.add_eq_max_of_ne (by rw [hn3L, h2x]; norm_num), hn3L, h2x]; norm_num
    apply hodd (-1)
    rw [hznorm, h2x, n₂, n₃]; norm_num
  · -- `v ≥ 2`: `x` even, `x − ℓ ≡ −ℓ` or `−5ℓ`, `x + 3ℓ ≡ 3ℓ` or `15ℓ` (S12 line 362)
    have h4 : ‖x‖ ≤ 1 / 4 := by
      rw [hxn]
      calc (2 : ℝ) ^ (-v) ≤ 2 ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 1 / 4 := by norm_num
    have hB' : SqEq (x - L) (-L) ∨ SqEq (x - L) (5 * -L) := by
      have := sqEq_add_or_five_two_adic (x := -L) (y := x) (neg_ne_zero.mpr hL0)
        (by rw [norm_neg, hL]; linarith)
      rwa [show -L + x = x - L by ring] at this
    have hA' : SqEq (x + 3 * L) (3 * L) ∨ SqEq (x + 3 * L) (5 * (3 * L)) := by
      have := sqEq_add_or_five_two_adic (x := 3 * L) (y := x) h3L0 (by rw [hn3L]; linarith)
      rwa [show 3 * L + x = x + 3 * L by ring] at this
    have bnd : ∀ k k' : ℕ, k < 2 → k' < 2 → 1 < 2 ∧ 1 < 2 ∧ k < 2 ∧ 1 < 2 ∧ k' < 2 :=
      fun k k' hk hk' => ⟨by norm_num, by norm_num, hk, by norm_num, hk'⟩
    rcases hA' with hA' | hA' <;> rcases hB' with hB' | hB'
    · exact key 1 1 0 1 0 (bnd 0 0 (by norm_num) (by norm_num))
        ((hxa'.symm.trans hA').trans_eq (by ring)) ((hxb'.symm.trans hB').trans_eq (by ring))
    · exact key 1 1 0 1 1 (bnd 0 1 (by norm_num) (by norm_num))
        ((hxa'.symm.trans hA').trans_eq (by ring)) ((hxb'.symm.trans hB').trans_eq (by ring))
    · exact key 1 1 1 1 0 (bnd 1 0 (by norm_num) (by norm_num))
        ((hxa'.symm.trans hA').trans_eq (by ring)) ((hxb'.symm.trans hB').trans_eq (by ring))
    · exact key 1 1 1 1 1 (bnd 1 1 (by norm_num) (by norm_num))
        ((hxa'.symm.trans hA').trans_eq (by ring)) ((hxb'.symm.trans hB').trans_eq (by ring))

/-- An odd integer is a `2`-adic unit, and `ℓ ≡ 3 (mod 4)` is not a `2`-adic square. -/
theorem not_isSquare_two_adic_of_mod4 {ℓ : ℤ} (h4 : ℓ % 4 = 3) : ¬ IsSquare (ℓ : ℚ_[2]) := by
  rw [isSquare_two_adic_intCast_iff (Int.odd_iff.mpr (by omega)),
    intCast_zmod_eq_of_emod (n := 8) (r := ℓ % 8) rfl]
  rcases (by omega : ℓ % 8 = 3 ∨ ℓ % 8 = 7) with h | h <;> rw [h] <;> decide

/-- The integer conclusion at `2`: from the classes to `a` odd and `b ≡ 1 (mod 4)`. -/
theorem localTwo_nec {ℓ a b : ℤ} (h4 : ℓ % 4 = 3) (ha : Squarefree a) (hb : Squarefree b)
    (h : LocM ℚ_[2] (ℓ : ℚ_[2]) a b) : a % 2 = 1 ∧ b % 4 = 1 := by
  have hL : ‖(ℓ : ℚ_[2])‖ = 1 := two_adic_norm_intCast_of_odd (Int.odd_iff.mpr (by omega))
  obtain ⟨⟨i, j, k, hi, hj, hk, hA⟩, j', k', hj', hk', hB⟩ :=
    locM_two_nec_classes hL (not_isSquare_two_adic_of_mod4 h4)
      (Int.cast_ne_zero.mpr ha.ne_zero) (Int.cast_ne_zero.mpr hb.ne_zero) h
  constructor
  · have hc : Odd (ℓ ^ i * 3 ^ j * 5 ^ k) :=
      (((Int.odd_iff.mpr (by omega)).pow).mul (Int.odd_iff.mpr rfl).pow).mul (Int.odd_iff.mpr rfl).pow
    have := not_dvd_of_sqEq_unit (p := 2) ha (two_adic_norm_intCast_of_odd hc)
      (hA.trans_eq (by push_cast; ring))
    omega
  · set c : ℤ := (-ℓ) ^ j' * 5 ^ k' with hcdef
    have hc4 : c % 4 = 1 := by
      interval_cases j' <;> interval_cases k' <;> simp only [hcdef, pow_zero, pow_one, one_mul,
        mul_one] <;> omega
    have hc : Odd c := Int.odd_iff.mpr (by omega)
    have hBc : SqEq (b : ℚ_[2]) (c : ℚ_[2]) := hB.trans_eq (by rw [hcdef]; push_cast; ring)
    have hb2 : ¬ ((2 : ℕ) : ℤ) ∣ b := not_dvd_of_sqEq_unit hb
      (two_adic_norm_intCast_of_odd hc) hBc
    have hbc : Odd (b * c) := (Int.odd_iff.mpr (by push_cast at hb2; omega)).mul hc
    have hsq : IsSquare (((b * c : ℤ)) : ℚ_[2]) := by push_cast; exact hBc.isSquare_mul
    have h8 := (isSquare_two_adic_intCast_iff hbc).mp hsq
    have h8' : (b * c) % 8 = 1 := by
      have := (ZMod.intCast_eq_intCast_iff' (b * c) 1 8).mp (by rw [h8]; simp)
      simpa using this
    have h4' : (b * c) % 4 = 1 := by generalize b * c = m at h8' ⊢; omega
    rw [Int.mul_emod, hc4, mul_one, Int.emod_emod_of_dvd b (by norm_num : (4 : ℤ) ∣ 4)] at h4'
    exact h4'

/-! ### Sufficiency at `2` -/

/-- **The four classes `τ · (5, 5)`** (`τ` a torsion class) are in the image over `ℚ₂`, for any
odd `ℓ`, with the rational witnesses `x = 1/4`, `ℓ + 80ℓ²`, `−3ℓ + 112ℓ²`, `20ℓ²` (DEPARTURE:
S12 asserts no sufficiency at `2`). -/
theorem locM_two_five {ℓ : ℤ} (hℓ : ℓ % 2 = 1) :
    LocM ℚ_[2] (ℓ : ℚ_[2]) 5 5 ∧ LocM ℚ_[2] (ℓ : ℚ_[2]) (5 * ℓ) 5 ∧
      LocM ℚ_[2] (ℓ : ℚ_[2]) 15 (-(5 * ℓ)) ∧ LocM ℚ_[2] (ℓ : ℚ_[2]) (15 * ℓ) (-(5 * ℓ)) := by
  have sq : ∀ (m n : ℤ) (c q : ℚ_[2]), n % 2 = 1 → m % 8 = n % 8 →
      q = (m : ℚ_[2]) / n * c ^ 2 → IsSquare q := fun m n c q hn h hq =>
    hq ▸ (isSquare_intCast_div_two_adic (Int.odd_iff.mpr hn) h).mul (IsSquare.sq c)
  have hL0 : (ℓ : ℚ_[2]) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `(5, 5)`, `x = 1/4`
    refine Or.inr ⟨1 / 4, ?_, ?_, ?_⟩
    · exact sq (1 + 12 * ℓ) 5 (1 / 2) _ rfl (by omega)
        (by push_cast; field_simp; ring)
    · exact sq (1 - 4 * ℓ) 5 (1 / 2) _ rfl (by omega)
        (by push_cast; field_simp; ring)
    · exact sq 1 1 (1 / 10) _ rfl rfl
        (by push_cast; field_simp; ring)
  · -- `(5ℓ, 5)`, `x = ℓ + 80ℓ²`
    refine Or.inr ⟨ℓ + 80 * ℓ ^ 2, ?_, ?_, ?_⟩
    · exact sq (1 + 20 * ℓ) 5 2 _ rfl (by omega)
        (by push_cast; field_simp; ring)
    · exact sq 1 1 (4 * ℓ) _ rfl rfl
        (by push_cast; field_simp; ring)
    · exact sq (1 + 80 * ℓ) 1 (1 / 5) _ rfl (by omega)
        (by push_cast; field_simp)
  · -- `(15, −5ℓ)`, `x = −3ℓ + 112ℓ²`
    refine Or.inr ⟨-3 * ℓ + 112 * ℓ ^ 2, ?_, ?_, ?_⟩
    · exact sq 7 15 (4 * ℓ) _ rfl rfl
        (by push_cast; field_simp; ring)
    · exact sq (1 - 28 * ℓ) 5 2 _ rfl (by omega)
        (by push_cast; field_simp; ring)
    · exact sq (3 - 112 * ℓ) 3 (1 / 5) _ rfl (by omega)
        (by push_cast; field_simp; ring)
  · -- `(15ℓ, −5ℓ)`, `x = 20ℓ²`
    refine Or.inr ⟨20 * ℓ ^ 2, ?_, ?_, ?_⟩
    · exact sq (20 * ℓ + 3) 15 1 _ rfl (by omega)
        (by push_cast; field_simp)
    · exact sq (1 - 20 * ℓ) 5 1 _ rfl (by omega)
        (by push_cast; field_simp; ring)
    · exact sq (-1) 15 2 _ rfl rfl
        (by push_cast; field_simp; ring)

/-- The residue bookkeeping mod `8`: for `ℓ ≡ 3 (mod 4)`, every pair (`a` odd, `b ≡ 1 (mod 4)`)
of residues is the residue pair of one of the eight classes. -/
theorem two_classes_mod8 : ∀ l x y : ZMod 8, (l = 3 ∨ l = 7) → (x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7) →
    (y = 1 ∨ y = 5) →
    (x = 1 ∧ y = 1) ∨ (x = l ∧ y = 1) ∨ (x = 3 ∧ y = -l) ∨ (x = 3 * l ∧ y = -l) ∨
      (x = 5 ∧ y = 5) ∨ (x = 5 * l ∧ y = 5) ∨ (x = 15 ∧ y = -(5 * l)) ∨
      (x = 15 * l ∧ y = -(5 * l)) := by
  decide

/-- **`LocalTwo`, "if"**: for `ℓ ≡ 3 (mod 4)`, `a` odd and `b ≡ 1 (mod 4)`, the class `(a, b)` is
in the image (DEPARTURE: S12 line 374 asserts no sufficiency at `2`; the descent uses only
the identity and torsion classes there). -/
theorem localTwo_suff {ℓ a b : ℤ} (h4 : ℓ % 4 = 3) (ha2 : a % 2 = 1) (hb4 : b % 4 = 1) :
    LocM ℚ_[2] (ℓ : ℚ_[2]) a b := by
  have hL0 : (ℓ : ℚ_[2]) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  have h30 : (3 : ℚ_[2]) ≠ 0 := by norm_num
  obtain ⟨h55, h5l, h15, h15l⟩ := locM_two_five (ℓ := ℓ) (by omega)
  have hl : (ℓ : ZMod 8) = 3 ∨ (ℓ : ZMod 8) = 7 := by
    rcases (by omega : ℓ % 8 = 3 ∨ ℓ % 8 = 7) with h | h
    · left; rw [intCast_zmod_eq_of_emod (n := 8) (by simpa using h)]; rfl
    · right; rw [intCast_zmod_eq_of_emod (n := 8) (by simpa using h)]; rfl
  have hx : (a : ZMod 8) = 1 ∨ (a : ZMod 8) = 3 ∨ (a : ZMod 8) = 5 ∨ (a : ZMod 8) = 7 := by
    rcases (by omega : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7) with h | h | h | h <;>
      rw [intCast_zmod_eq_of_emod (n := 8) (by simpa using h)] <;> simp
  have hy : (b : ZMod 8) = 1 ∨ (b : ZMod 8) = 5 := by
    rcases (by omega : b % 8 = 1 ∨ b % 8 = 5) with h | h <;>
      rw [intCast_zmod_eq_of_emod (n := 8) (by simpa using h)] <;> simp
  -- `fin`: from residues to square classes in `ℚ₂`
  have fin : ∀ c₁ c₂ : ℤ, c₁ % 2 = 1 → c₂ % 2 = 1 → (a : ZMod 8) = c₁ → (b : ZMod 8) = c₂ →
      LocM ℚ_[2] (ℓ : ℚ_[2]) c₁ c₂ → LocM ℚ_[2] (ℓ : ℚ_[2]) a b := by
    intro c₁ c₂ hc₁ hc₂ e₁ e₂ hloc
    have ha : SqEq (a : ℚ_[2]) (c₁ : ℚ_[2]) :=
      sqEq_of_isSquare_div (Int.cast_ne_zero.mpr (by omega)) (Int.cast_ne_zero.mpr (by omega))
        (isSquare_intCast_div_two_adic (Int.odd_iff.mpr hc₁)
          ((ZMod.intCast_eq_intCast_iff' a c₁ 8).mp e₁))
    have hb : SqEq (b : ℚ_[2]) (c₂ : ℚ_[2]) :=
      sqEq_of_isSquare_div (Int.cast_ne_zero.mpr (by omega)) (Int.cast_ne_zero.mpr (by omega))
        (isSquare_intCast_div_two_adic (Int.odd_iff.mpr hc₂)
          ((ZMod.intCast_eq_intCast_iff' b c₂ 8).mp e₂))
    exact (locM_congr_sq ha hb).mpr hloc
  rcases two_classes_mod8 _ _ _ hl hx hy with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ |
    ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · exact fin 1 1 rfl rfl (by rw [e₁]; simp) (by rw [e₂]; simp) (by simpa using locM_one_one _)
  · exact fin ℓ 1 (by omega) rfl (by rw [e₁]) (by rw [e₂]; simp)
      (by simpa using locM_tau1 hL0)
  · exact fin 3 (-ℓ) rfl (by omega) (by rw [e₁]; simp) (by rw [e₂]; simp)
      (by simpa using locM_tau2 h30 hL0)
  · exact fin (3 * ℓ) (-ℓ) (by omega) (by omega) (by rw [e₁]; simp) (by rw [e₂]; simp)
      (by simpa using locM_tau12 h30 hL0)
  · exact fin 5 5 rfl rfl (by rw [e₁]; simp) (by rw [e₂]; simp) (by simpa using h55)
  · exact fin (5 * ℓ) 5 (by omega) rfl (by rw [e₁]; simp) (by rw [e₂]; simp) (by simpa using h5l)
  · exact fin 15 (-(5 * ℓ)) rfl (by omega) (by rw [e₁]; simp) (by rw [e₂]; simp)
      (by simpa using h15)
  · exact fin (15 * ℓ) (-(5 * ℓ)) (by omega) (by omega) (by rw [e₁]; simp) (by rw [e₂]; simp)
      (by simpa using h15l)

/-- **`LocalTwo` holds.** -/
theorem localTwo : LocalTwo := by
  intro ℓ a b _ h4 ha hb
  have e : LocM ℚ_[2] (ℓ : ℚ_[2]) a b ↔ LocM ℚ_[2] (((ℓ : ℤ)) : ℚ_[2]) a b := by simp
  have h4' : (ℓ : ℤ) % 4 = 3 := by omega
  rw [e]
  exact ⟨localTwo_nec h4' ha hb, fun h => localTwo_suff h4' h.1 h.2⟩

/-- **S12's necessary condition at `2`, as stated there** (lines 359–374): both Kummer coordinates
of a local class have even valuation, i.e. the squarefree `a` and `b` are odd. A corollary of
`localTwo_nec`; this is all that S12 asserts at `2`. -/
theorem localTwo_S12 {ℓ : ℕ} {a b : ℤ} (h4 : ℓ % 4 = 3) (ha : Squarefree a) (hb : Squarefree b)
    (h : LocM ℚ_[2] ℓ a b) : a % 2 = 1 ∧ b % 2 = 1 := by
  have h' : LocM ℚ_[2] (((ℓ : ℤ)) : ℚ_[2]) a b := by simpa using h
  obtain ⟨h1, h2⟩ := localTwo_nec (by omega) ha hb h'
  exact ⟨h1, by omega⟩

end ZInQ.Manuscript.PoleRC
