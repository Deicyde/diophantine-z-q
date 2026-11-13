import ZInQKernel.Hypotheses.MordellWeil

/-!
# Sizes under quadratic-field operations

Blueprint: `size/norms/quadratic-heights.md`.

An integer triple `(a, b, c)` with `c ≠ 0` represents `(a + b s)/c ∈ K₀` and has size
`max (|a|, |b|, |c|)` (`QRep`). If `u, u'` are represented by triples of size at most `H ≥ 2`,
then `u ± u'`, `u u'`, `2u` and (for `u' ≠ 0`) `u / u'` are represented by triples of size at
most `3H⁴`, and the reduced numerators and denominators of the rational coordinates of a
represented element are bounded by the size of the triple.
-/

namespace ZInQ.Size

/-- An integer triple `(a, b, c)`, `c ≠ 0`, representing `(a + b s)/c ∈ K₀`. -/
structure QRep where
  a : ℤ
  b : ℤ
  c : ℤ
  hc : c ≠ 0

namespace QRep

/-- The represented element `(a + b s)/c = a/c + (b/c) s`. -/
def val (r : QRep) : K0 := ⟨r.a / r.c, r.b / r.c⟩

/-- The size `max (|a|, |b|, |c|)`. -/
def size (r : QRep) : ℕ := max r.a.natAbs (max r.b.natAbs r.c.natAbs)

theorem size_le_iff {r : QRep} {H : ℕ} :
    r.size ≤ H ↔ |r.a| ≤ H ∧ |r.b| ≤ H ∧ |r.c| ≤ H := by
  simp only [size, max_le_iff, Int.abs_eq_natAbs, Nat.cast_le]

theorem cast_c_ne_zero (r : QRep) : (r.c : ℚ) ≠ 0 := Int.cast_ne_zero.2 r.hc

/-! ### The operations -/

/-- `(a + b s)/c + (a' + b' s)/c' = ((ac' + a'c) + (bc' + b'c) s)/(cc')`. -/
def add (r r' : QRep) : QRep :=
  ⟨r.a * r'.c + r'.a * r.c, r.b * r'.c + r'.b * r.c, r.c * r'.c, mul_ne_zero r.hc r'.hc⟩

/-- `(a + b s)/c - (a' + b' s)/c' = ((ac' - a'c) + (bc' - b'c) s)/(cc')`. -/
def sub (r r' : QRep) : QRep :=
  ⟨r.a * r'.c - r'.a * r.c, r.b * r'.c - r'.b * r.c, r.c * r'.c, mul_ne_zero r.hc r'.hc⟩

/-- `(a + b s)/c · (a' + b' s)/c' = ((aa' + 2bb') + (ab' + a'b) s)/(cc')`. -/
def mul (r r' : QRep) : QRep :=
  ⟨r.a * r'.a + 2 * r.b * r'.b, r.a * r'.b + r'.a * r.b, r.c * r'.c, mul_ne_zero r.hc r'.hc⟩

/-- `2 (a + b s)/c = (2a + 2b s)/c`. -/
def two_mul (r : QRep) : QRep := ⟨2 * r.a, 2 * r.b, r.c, r.hc⟩

/-- `a'² - 2b'² ≠ 0` unless `a' = b' = 0`, as `√2` is irrational. -/
theorem norm_ne_zero {a b : ℤ} (h : a ≠ 0 ∨ b ≠ 0) : a ^ 2 - 2 * b ^ 2 ≠ 0 := by
  intro h0
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [ne_eq, not_true_eq_false, or_false] at h
    apply h
    simpa using h0
  · apply not_isSquare_two_rat
    refine ⟨(a : ℚ) / b, ?_⟩
    have hb' : (b : ℚ) ≠ 0 := Int.cast_ne_zero.2 hb
    have : (a : ℚ) ^ 2 = 2 * b ^ 2 := by exact_mod_cast sub_eq_zero.1 h0
    field_simp
    linear_combination -this

/-- The quotient by the conjugate:
`u / u' = c' ((aa' - 2bb') + (a'b - ab') s) / (c (a'² - 2b'²))`. -/
def div (r r' : QRep) (h : r'.a ≠ 0 ∨ r'.b ≠ 0) : QRep :=
  ⟨r'.c * (r.a * r'.a - 2 * r.b * r'.b), r'.c * (r'.a * r.b - r.a * r'.b),
    r.c * (r'.a ^ 2 - 2 * r'.b ^ 2), mul_ne_zero r.hc (norm_ne_zero h)⟩

theorem val_add (r r' : QRep) : (add r r').val = r.val + r'.val := by
  have := r.cast_c_ne_zero; have := r'.cast_c_ne_zero
  ext <;> simp [val, add] <;> field_simp

theorem val_sub (r r' : QRep) : (sub r r').val = r.val - r'.val := by
  have := r.cast_c_ne_zero; have := r'.cast_c_ne_zero
  ext <;> simp [val, sub] <;> field_simp

theorem val_mul (r r' : QRep) : (mul r r').val = r.val * r'.val := by
  have := r.cast_c_ne_zero; have := r'.cast_c_ne_zero
  ext <;> simp [val, mul] <;> field_simp

theorem val_two_mul (r : QRep) : (two_mul r).val = 2 * r.val := by
  have := r.cast_c_ne_zero
  ext <;> simp [val, two_mul, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> field_simp

theorem ne_zero_of_val_ne_zero {r : QRep} (h : r.val ≠ 0) : r.a ≠ 0 ∨ r.b ≠ 0 := by
  by_contra h'
  push Not at h'
  apply h
  ext <;> simp [val, h'.1, h'.2]

theorem val_div (r r' : QRep) (h : r'.val ≠ 0) :
    (div r r' (ne_zero_of_val_ne_zero h)).val = r.val / r'.val := by
  have hc := r.cast_c_ne_zero
  have hc' := r'.cast_c_ne_zero
  have hN : ((r'.a : ℚ) ^ 2 - 2 * r'.b ^ 2) ≠ 0 := by
    exact_mod_cast norm_ne_zero (ne_zero_of_val_ne_zero h)
  rw [eq_div_iff h]
  ext <;> simp [val, div] <;> field_simp <;> ring

/-! ### Sizes -/

section sizes

variable {r r' : QRep} {H : ℕ}

private theorem abs_mul_le {x y : ℤ} (hx : |x| ≤ H) (hy : |y| ≤ H) : |x * y| ≤ (H : ℤ) ^ 2 := by
  rw [abs_mul, sq]
  exact mul_le_mul hx hy (abs_nonneg _) (by positivity)

private theorem pow_le_pow4 (hH : 2 ≤ H) {k : ℕ} (hk : k ≤ 4) : (H : ℤ) ^ k ≤ (H : ℤ) ^ 4 :=
  pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ H)) hk

theorem size_add_le (h : r.size ≤ H) (h' : r'.size ≤ H) : (add r r').size ≤ 2 * H ^ 2 := by
  rw [size_le_iff] at *
  obtain ⟨ha, hb, hc⟩ := h; obtain ⟨ha', hb', hc'⟩ := h'
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · exact (abs_add_le _ _).trans (by linarith [abs_mul_le ha hc', abs_mul_le ha' hc])
  · exact (abs_add_le _ _).trans (by linarith [abs_mul_le hb hc', abs_mul_le hb' hc])
  · have := abs_mul_le hc hc'
    change |r.c * r'.c| ≤ _
    nlinarith [sq_nonneg (H : ℤ)]

theorem size_sub_le (h : r.size ≤ H) (h' : r'.size ≤ H) : (sub r r').size ≤ 2 * H ^ 2 := by
  rw [size_le_iff] at *
  obtain ⟨ha, hb, hc⟩ := h; obtain ⟨ha', hb', hc'⟩ := h'
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · exact (abs_sub _ _).trans (by linarith [abs_mul_le ha hc', abs_mul_le ha' hc])
  · exact (abs_sub _ _).trans (by linarith [abs_mul_le hb hc', abs_mul_le hb' hc])
  · have := abs_mul_le hc hc'
    change |r.c * r'.c| ≤ _
    nlinarith [sq_nonneg (H : ℤ)]

theorem size_mul_le (h : r.size ≤ H) (h' : r'.size ≤ H) : (mul r r').size ≤ 3 * H ^ 2 := by
  rw [size_le_iff] at *
  obtain ⟨ha, hb, hc⟩ := h; obtain ⟨ha', hb', hc'⟩ := h'
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · refine (abs_add_le _ _).trans ?_
    have : |2 * r.b * r'.b| = 2 * |r.b * r'.b| := by rw [mul_assoc, abs_mul]; norm_num
    rw [this]
    linarith [abs_mul_le ha ha', abs_mul_le hb hb']
  · exact (abs_add_le _ _).trans (by nlinarith [abs_mul_le ha hb', abs_mul_le ha' hb])
  · have := abs_mul_le hc hc'
    change |r.c * r'.c| ≤ _
    nlinarith [sq_nonneg (H : ℤ)]

theorem size_two_mul_le (h : r.size ≤ H) : (two_mul r).size ≤ 2 * H := by
  rw [size_le_iff] at *
  obtain ⟨ha, hb, hc⟩ := h
  push_cast
  simp only [two_mul, abs_mul, abs_two]
  refine ⟨by linarith, by linarith, by linarith [abs_nonneg r.c]⟩

theorem size_div_le (h : r.size ≤ H) (h' : r'.size ≤ H) (h0 : r'.a ≠ 0 ∨ r'.b ≠ 0) :
    (div r r' h0).size ≤ 3 * H ^ 3 := by
  rw [size_le_iff] at *
  obtain ⟨ha, hb, hc⟩ := h; obtain ⟨ha', hb', hc'⟩ := h'
  have hH : (0 : ℤ) ≤ H := by positivity
  have key : ∀ {x y z w v : ℤ}, |x| ≤ H → |y * z| ≤ (H : ℤ) ^ 2 → |w * v| ≤ (H : ℤ) ^ 2 →
      |x * (y * z - 2 * (w * v))| ≤ 3 * (H : ℤ) ^ 3 := by
    intro x y z w v hx h1 h2
    rw [abs_mul]
    have : |y * z - 2 * (w * v)| ≤ 3 * (H : ℤ) ^ 2 := by
      refine (abs_sub _ _).trans ?_
      have e2 : |2 * (w * v)| = 2 * |w * v| := by rw [abs_mul, abs_two]
      rw [e2]
      linarith
    calc |x| * |y * z - 2 * (w * v)| ≤ H * (3 * (H : ℤ) ^ 2) :=
          mul_le_mul hx this (abs_nonneg _) hH
      _ = 3 * (H : ℤ) ^ 3 := by ring
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · simp only [div]
    rw [show r.a * r'.a - 2 * r.b * r'.b = r.a * r'.a - 2 * (r.b * r'.b) by ring]
    exact key hc' (abs_mul_le ha ha') (abs_mul_le hb hb')
  · simp only [div]
    rw [abs_mul]
    have h1 := abs_mul_le ha' hb
    have h2 := abs_mul_le ha hb'
    have : |r'.a * r.b - r.a * r'.b| ≤ 3 * (H : ℤ) ^ 2 :=
      (abs_sub _ _).trans (by linarith [sq_nonneg (H : ℤ)])
    calc |r'.c| * |r'.a * r.b - r.a * r'.b| ≤ H * (3 * (H : ℤ) ^ 2) :=
          mul_le_mul hc' this (abs_nonneg _) hH
      _ = 3 * (H : ℤ) ^ 3 := by ring
  · simp only [div]
    rw [show r'.a ^ 2 - 2 * r'.b ^ 2 = r'.a * r'.a - 2 * (r'.b * r'.b) by ring]
    exact key hc (abs_mul_le ha' ha') (abs_mul_le hb' hb')

theorem size_le_of_le_three (hH : 2 ≤ H) {r : QRep} {k : ℕ} (hk : k ≤ 4) {m : ℕ} (hm : m ≤ 3)
    (h : r.size ≤ m * H ^ k) : r.size ≤ 3 * H ^ 4 := by
  refine h.trans ?_
  have h1 : H ^ k ≤ H ^ 4 := Nat.pow_le_pow_right (by omega) hk
  exact Nat.mul_le_mul hm h1

end sizes

/-- **Sizes under quadratic-field operations**, items (1) and (2). -/
theorem exists_add (r r' : QRep) {H : ℕ} (hH : 2 ≤ H) (h : r.size ≤ H) (h' : r'.size ≤ H) :
    ∃ q : QRep, q.val = r.val + r'.val ∧ q.size ≤ 3 * H ^ 4 :=
  ⟨add r r', val_add r r', size_le_of_le_three hH (by norm_num) (by norm_num) (size_add_le h h')⟩

theorem exists_sub (r r' : QRep) {H : ℕ} (hH : 2 ≤ H) (h : r.size ≤ H) (h' : r'.size ≤ H) :
    ∃ q : QRep, q.val = r.val - r'.val ∧ q.size ≤ 3 * H ^ 4 :=
  ⟨sub r r', val_sub r r', size_le_of_le_three hH (by norm_num) (by norm_num) (size_sub_le h h')⟩

theorem exists_mul (r r' : QRep) {H : ℕ} (hH : 2 ≤ H) (h : r.size ≤ H) (h' : r'.size ≤ H) :
    ∃ q : QRep, q.val = r.val * r'.val ∧ q.size ≤ 3 * H ^ 4 :=
  ⟨mul r r', val_mul r r', size_le_of_le_three hH (by norm_num) (by norm_num) (size_mul_le h h')⟩

theorem exists_two_mul (r : QRep) {H : ℕ} (hH : 2 ≤ H) (h : r.size ≤ H) :
    ∃ q : QRep, q.val = 2 * r.val ∧ q.size ≤ 3 * H ^ 4 :=
  ⟨two_mul r, val_two_mul r, size_le_of_le_three hH (k := 1) (m := 2) (by norm_num) (by norm_num)
    (by simpa using size_two_mul_le h)⟩

theorem exists_div (r r' : QRep) {H : ℕ} (hH : 2 ≤ H) (h : r.size ≤ H) (h' : r'.size ≤ H)
    (h0 : r'.val ≠ 0) : ∃ q : QRep, q.val = r.val / r'.val ∧ q.size ≤ 3 * H ^ 4 :=
  ⟨div r r' (ne_zero_of_val_ne_zero h0), val_div r r' h0,
    size_le_of_le_three hH (by norm_num) (by norm_num) (size_div_le h h' _)⟩

/-! ### Reduced coordinates -/

/-- The reduced numerator and denominator of `a / c` are bounded by `|a|` and `|c|`. -/
theorem num_den_div_le (a c : ℤ) (hc : c ≠ 0) :
    ((a : ℚ) / c).num.natAbs ≤ a.natAbs ∧ ((a : ℚ) / c).den ≤ c.natAbs := by
  rw [← Rat.divInt_eq_div]
  constructor
  · rcases eq_or_ne a 0 with rfl | ha
    · simp
    · exact Nat.le_of_dvd (Int.natAbs_pos.2 ha)
        (Int.natAbs_dvd_natAbs.2 (Rat.num_dvd a hc))
  · have := Int.natAbs_dvd_natAbs.2 (Rat.den_dvd a c)
    rw [Int.natAbs_natCast] at this
    exact Nat.le_of_dvd (Int.natAbs_pos.2 hc) this

/-- **Sizes under quadratic-field operations**, item (3): if `(a, b, c)` represents
`u = u₀ + u₁ s`, then `u₀ = a/c`, `u₁ = b/c`, and their reduced numerators and positive reduced
denominators are bounded by the size. -/
theorem coord_bounds (r : QRep) :
    r.val.re = r.a / r.c ∧ r.val.im = r.b / r.c ∧
    (r.val.re.num.natAbs ≤ r.size ∧ r.val.re.den ≤ r.size) ∧
    (r.val.im.num.natAbs ≤ r.size ∧ r.val.im.den ≤ r.size) := by
  have h1 := num_den_div_le r.a r.c r.hc
  have h2 := num_den_div_le r.b r.c r.hc
  refine ⟨rfl, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [val, size] <;> omega

end QRep

end ZInQ.Size
