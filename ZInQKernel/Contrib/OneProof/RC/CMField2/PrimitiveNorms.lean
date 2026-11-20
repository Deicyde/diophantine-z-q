import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The primitive norm spectrum distinguishes normalized imaginary quadratic
orders, including the two extra-unit cases. On-the-spot calculation (c). -/

namespace ZInQ.Manuscript.RC.CMField2

/-- Nontrivial primitive indices for the basis `1, ω` with trace `t` and
norm `u`. The trace is normalized to 0 or 1 by translating `ω`. -/
def primitiveNormLevels (t u : ℤ) : Set ℤ :=
  {m | 1 < m ∧ ∃ a b : ℤ, Int.gcd a b = 1 ∧ a ^ 2 + t * a * b + u * b ^ 2 = m}

private theorem min_generic {t u m : ℤ} (ht : t = 0 ∨ t = 1) (hu : 2 ≤ u)
    (hm : m ∈ primitiveNormLevels t u) : u ≤ m := by
  obtain ⟨hm, a, b, hg, he⟩ := hm
  have hb : b ≠ 0 := by
    intro hb
    subst b
    simp at hg he
    have : a = -1 ∨ a = 1 := by omega
    rcases this with rfl | rfl <;> norm_num at he <;> omega
  rcases ht with rfl | rfl
  · have hbs : 1 ≤ b ^ 2 := by
      by_cases h : 0 < b
      · exact one_le_pow₀ (by omega) (n := 2)
      · have hp : 1 ≤ -b := by omega
        simpa using (one_le_pow₀ hp (n := 2))
    nlinarith [mul_nonneg (show 0 ≤ u by omega) (sub_nonneg.mpr hbs), sq_nonneg a]
  · have hpar (x : ℤ) : 0 ≤ x ^ 2 + x := by
      by_cases hx : 0 ≤ x
      · exact add_nonneg (sq_nonneg x) hx
      · nlinarith [mul_nonneg (show 0 ≤ -x by omega) (show 0 ≤ -x - 1 by omega)]
    by_cases h1 : b = 1
    · subst b; nlinarith [hpar a]
    by_cases hn1 : b = -1
    · subst b; nlinarith [hpar (-a)]
    have hbs : 4 ≤ b ^ 2 := by
      have h : 2 ≤ b ∨ b ≤ -2 := by omega
      rcases h with h | h
      · nlinarith [mul_nonneg (show 0 ≤ b - 2 by omega) (show 0 ≤ b + 2 by omega)]
      · nlinarith [mul_nonneg (show 0 ≤ -b - 2 by omega) (show 0 ≤ -b + 2 by omega)]
    nlinarith [sq_nonneg (2 * a + b),
      mul_nonneg (show 0 ≤ 4 * u - 1 by omega) (sub_nonneg.mpr hbs)]

private theorem generic_trace_one_gap {u : ℤ} (hu : 2 ≤ u) :
    u + 1 ∉ primitiveNormLevels 1 u := by
  rintro ⟨_, a, b, hg, he⟩
  have hpar (x : ℤ) : x ^ 2 + x ≠ 1 := by
    intro h
    have hx : x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ 1 ≤ x := by omega
    rcases hx with hx | rfl | rfl | hx
    · nlinarith [mul_nonneg (show 0 ≤ -x - 2 by omega) (show 0 ≤ -x + 1 by omega)]
    · norm_num at h
    · norm_num at h
    · nlinarith [mul_nonneg (show 0 ≤ x - 1 by omega) (show 0 ≤ x + 2 by omega)]
  have hb : b = 0 ∨ b = 1 ∨ b = -1 ∨ 2 ≤ b ∨ b ≤ -2 := by omega
  rcases hb with rfl | rfl | rfl | hb | hb
  · simp at hg he
    have : a = -1 ∨ a = 1 := by omega
    rcases this with rfl | rfl <;> norm_num at he <;> omega
  · exact hpar a (by nlinarith)
  · exact hpar (-a) (by nlinarith)
  all_goals
    have hbs : 4 ≤ b ^ 2 := by
      first
      | nlinarith [mul_nonneg (show 0 ≤ b - 2 by omega) (show 0 ≤ b + 2 by omega)]
      | nlinarith [mul_nonneg (show 0 ≤ -b - 2 by omega) (show 0 ≤ -b + 2 by omega)]
    nlinarith [sq_nonneg (2 * a + b),
      mul_nonneg (show 0 ≤ 4 * u - 1 by omega) (sub_nonneg.mpr hbs)]

private theorem not_primitive_of_even {a b : ℤ} (ha : (2 : ℤ) ∣ a) (hb : (2 : ℤ) ∣ b) :
    Int.gcd a b ≠ 1 := by
  intro h
  have h' := Int.dvd_coe_gcd ha hb
  rw [h] at h'
  norm_num at h'

private theorem gaussian_no_three : 3 ∉ primitiveNormLevels 0 1 := by
  rintro ⟨_, a, b, _, h⟩
  have hx : ∀ x y : ZMod 4, x ^ 2 + y ^ 2 ≠ 3 := by decide
  apply hx (a : ZMod 4) (b : ZMod 4)
  simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using
    congrArg (fun n : ℤ => (n : ZMod 4)) (show a ^ 2 + b ^ 2 = 3 by simpa using h)

private theorem gaussian_no_four : 4 ∉ primitiveNormLevels 0 1 := by
  rintro ⟨_, a, b, hg, h⟩
  have h4 : ∀ x y : ZMod 4, x ^ 2 + y ^ 2 = 0 → (2 : ℕ) ∣ x.val ∧ (2 : ℕ) ∣ y.val := by
    decide
  have he : (a : ZMod 4) ^ 2 + (b : ZMod 4) ^ 2 = (4 : ZMod 4) := by
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using
      congrArg (fun n : ℤ => (n : ZMod 4)) (show a ^ 2 + b ^ 2 = 4 by simpa using h)
  rw [show (4 : ZMod 4) = 0 by decide] at he
  obtain ⟨ha, hb⟩ := h4 (a : ZMod 4) (b : ZMod 4) he
  have ha' := Int.natCast_dvd_natCast.mpr ha
  have hb' := Int.natCast_dvd_natCast.mpr hb
  rw [ZMod.val_intCast] at ha' hb'
  exact not_primitive_of_even (by omega) (by omega) hg

private theorem eisenstein_no_four : 4 ∉ primitiveNormLevels 1 1 := by
  rintro ⟨_, a, b, hg, h⟩
  have h2 : ∀ x y : ZMod 2, x ^ 2 + x * y + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
  have he : (a : ZMod 2) ^ 2 + (a : ZMod 2) * (b : ZMod 2) + (b : ZMod 2) ^ 2 =
      (4 : ZMod 2) := by
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using
      congrArg (fun n : ℤ => (n : ZMod 2)) (show a ^ 2 + a * b + b ^ 2 = 4 by simpa using h)
  rw [show (4 : ZMod 2) = 0 by decide] at he
  obtain ⟨ha, hb⟩ := h2 _ _ he
  exact not_primitive_of_even ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb) hg

private theorem eisenstein_no_mod_three {m : ℤ} (hm : (m : ZMod 3) = 2) :
    m ∉ primitiveNormLevels 1 1 := by
  rintro ⟨_, a, b, _, h⟩
  have h3 : ∀ x y : ZMod 3, x ^ 2 + x * y + y ^ 2 ≠ 2 := by decide
  apply h3 (a : ZMod 3) (b : ZMod 3)
  have he : (a : ZMod 3) ^ 2 + (a : ZMod 3) * (b : ZMod 3) + (b : ZMod 3) ^ 2 =
      (m : ZMod 3) := by
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul] using
      congrArg (fun n : ℤ => (n : ZMod 3)) (show a ^ 2 + a * b + b ^ 2 = m by simpa using h)
  exact he.trans hm

/-- The primitive norm sets determine trace and norm in normalized bases.
No multiplicity information is necessary, even at the extra-unit orders. -/
theorem quadraticNormParameters_eq_of_primitiveNormLevels {t₁ t₂ u₁ u₂ : ℤ}
    (ht₁ : t₁ = 0 ∨ t₁ = 1) (ht₂ : t₂ = 0 ∨ t₂ = 1) (hu₁ : 1 ≤ u₁) (hu₂ : 1 ≤ u₂)
    (h : primitiveNormLevels t₁ u₁ = primitiveNormLevels t₂ u₂) :
    t₁ = t₂ ∧ u₁ = u₂ := by
  have mem {t u : ℤ} (_ht : t = 0 ∨ t = 1) (hu : 2 ≤ u) :
      u ∈ primitiveNormLevels t u := ⟨by omega, 0, 1, by decide, by ring⟩
  have gauss : 2 ∈ primitiveNormLevels 0 1 := ⟨by decide, 1, 1, by decide, by decide⟩
  have eisen : 3 ∈ primitiveNormLevels 1 1 := ⟨by decide, 1, 1, by decide, by decide⟩
  have exceptional {t v u : ℤ} (ht : t = 0 ∨ t = 1) (hv : v = 0 ∨ v = 1) (hu : 2 ≤ u)
      (he : primitiveNormLevels t 1 = primitiveNormLevels v u) : False := by
    rcases ht with rfl | rfl
    · have hue : u = 2 := by
        have := min_generic hv hu (he ▸ gauss)
        omega
      subst u
      rcases hv with rfl | rfl
      · exact gaussian_no_three (he.symm ▸ (show 3 ∈ primitiveNormLevels 0 2 from
          ⟨by decide, 1, 1, by decide, by decide⟩))
      · exact gaussian_no_four (he.symm ▸ (show 4 ∈ primitiveNormLevels 1 2 from
          ⟨by decide, 1, 1, by decide, by decide⟩))
    · have hhi : u ≤ 3 := min_generic hv hu (he ▸ eisen)
      have hlo : u ≠ 2 := by
        intro e; subst u
        exact eisenstein_no_mod_three (show ((2 : ℤ) : ZMod 3) = 2 by decide) (he.symm ▸ mem hv hu)
      have hue : u = 3 := by omega
      subst u
      rcases hv with rfl | rfl
      · exact eisenstein_no_four (he.symm ▸ (show 4 ∈ primitiveNormLevels 0 3 from
          ⟨by decide, 1, 1, by decide, by decide⟩))
      · exact eisenstein_no_mod_three (show ((5 : ℤ) : ZMod 3) = 2 by decide)
          (he.symm ▸ (show 5 ∈ primitiveNormLevels 1 3 from ⟨by decide, 1, 1, by decide, by decide⟩))
  by_cases e₁ : u₁ = 1
  · subst u₁
    by_cases e₂ : u₂ = 1
    · subst u₂
      refine ⟨?_, rfl⟩
      rcases ht₁ with rfl | rfl <;> rcases ht₂ with rfl | rfl
      · rfl
      · exact (eisenstein_no_mod_three (show ((2 : ℤ) : ZMod 3) = 2 by decide) (h ▸ gauss)).elim
      · exact (gaussian_no_three (h ▸ eisen)).elim
      · rfl
    · exact (exceptional ht₁ ht₂ (by omega) h).elim
  have hu : 2 ≤ u₁ := by omega
  by_cases e₂ : u₂ = 1
  · subst u₂; exact (exceptional ht₂ ht₁ hu h.symm).elim
  have hv : 2 ≤ u₂ := by omega
  have he : u₁ = u₂ := le_antisymm (min_generic ht₁ hu (h.symm ▸ mem ht₂ hv))
    (min_generic ht₂ hv (h ▸ mem ht₁ hu))
  subst u₂
  have hgap : u₁ + 1 ∈ primitiveNormLevels 0 u₁ :=
    ⟨by omega, 1, 1, by decide, by ring⟩
  refine ⟨?_, rfl⟩
  rcases ht₁ with rfl | rfl <;> rcases ht₂ with rfl | rfl
  · rfl
  · exact (generic_trace_one_gap hu (h ▸ hgap)).elim
  · exact (generic_trace_one_gap hu (h.symm ▸ hgap)).elim
  · rfl


end ZInQ.Manuscript.RC.CMField2
