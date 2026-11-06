import ZInQKernel.Model.Field.SpecialPrimes

/-!
# A dyadic valuation computation

Blueprint: `model/field/dyadic-valuation.md`.

1. For `A, B ∈ ℚ` with `v₂(A) = 0` and `v₂(B) ≥ 0`: `v_s((A + B s)² + 1) = 2` if `v₂(B) ≥ 1`
   (including `B = 0`), and `= 3` if `v₂(B) = 0`.
2. For `a, b ∈ ℤ[s]` with `s ∤ a`, `s ∤ b`: `v_s(a² + δ² b²) ∈ {2, 3}`.

The proofs are integral: `v_s(R + I s)` for integers `R, I` is read off from `R` and `I`
modulo `4`, and the residues are checked by `decide`.
-/

namespace ZInQ

open QuadraticAlgebra

/-! ### `v_s` of `R + I s` from residues modulo 4 -/

theorem Zs.intCast_dvd_iff (n : ℤ) (z : Zs) : (n : Zs) ∣ z ↔ n ∣ z.re ∧ n ∣ z.im := by
  rw [← eq_intCast (algebraMap ℤ Zs), QuadraticAlgebra.algebraMap_dvd_iff]

theorem sqrt2Z_sq : sqrt2Z ^ 2 = (2 : ℤ) := by ext <;> simp [sqrt2Z, pow_two]
theorem sqrt2Z_pow_four : sqrt2Z ^ 4 = (4 : ℤ) := by ext <;> simp [sqrt2Z, pow_succ]

theorem sqrt2Z_pow_two_dvd_iff (z : Zs) : sqrt2Z ^ 2 ∣ z ↔ 2 ∣ z.re ∧ 2 ∣ z.im := by
  rw [sqrt2Z_sq, Zs.intCast_dvd_iff]

theorem sqrt2Z_pow_three_dvd_iff (z : Zs) : sqrt2Z ^ 3 ∣ z ↔ 4 ∣ z.re ∧ 2 ∣ z.im := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨⟨w.im, ?_⟩, ⟨w.re, ?_⟩⟩ <;> simp [sqrt2Z, pow_succ]
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    exact ⟨⟨i, r⟩, by ext <;> simp [sqrt2Z, pow_succ, hr, hi]⟩

theorem sqrt2Z_pow_four_dvd_iff (z : Zs) : sqrt2Z ^ 4 ∣ z ↔ 4 ∣ z.re ∧ 4 ∣ z.im := by
  rw [sqrt2Z_pow_four, Zs.intCast_dvd_iff]

theorem dvd_four_iff_zmod (x : ℤ) (r : ℤ) : 4 ∣ x - r ↔ ((x : ZMod 4) = (r : ZMod 4)) := by
  rw [← sub_eq_zero, ← Int.cast_sub, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem vS_mk_eq_two {R I : ℤ} (hR' : (R : ZMod 4) = 2) (hI' : (I : ZMod 4) = 0) :
    vp sqrt2Z (Zs.toK0 ⟨R, I⟩) = 2 := by
  have hR : 4 ∣ R - 2 := (dvd_four_iff_zmod R 2).mpr (by simpa using hR')
  have hI : 4 ∣ I - 0 := (dvd_four_iff_zmod I 0).mpr (by simpa using hI')
  have hz : (⟨R, I⟩ : Zs) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; simp at this; omega
  have key := vp_eq_iff prime_sqrt2Z hz 2
  rw [sqrt2Z_pow_two_dvd_iff, sqrt2Z_pow_three_dvd_iff] at key
  simp only [Nat.cast_ofNat] at key
  rw [key]
  omega

theorem vS_mk_eq_three {R I : ℤ} (hR' : (R : ZMod 4) = 0) (hI' : (I : ZMod 4) = 2) :
    vp sqrt2Z (Zs.toK0 ⟨R, I⟩) = 3 := by
  have hR : 4 ∣ R - 0 := (dvd_four_iff_zmod R 0).mpr (by simpa using hR')
  have hI : 4 ∣ I - 2 := (dvd_four_iff_zmod I 2).mpr (by simpa using hI')
  have hz : (⟨R, I⟩ : Zs) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.im h; simp at this; omega
  have key := vp_eq_iff prime_sqrt2Z hz 3
  rw [sqrt2Z_pow_three_dvd_iff, sqrt2Z_pow_four_dvd_iff] at key
  simp only [Nat.cast_ofNat] at key
  rw [key]
  omega

theorem odd_zmod_four {x : ℤ} (hx : ¬ (2 : ℤ) ∣ x) : (x : ZMod 4) = 1 ∨ (x : ZMod 4) = 3 := by
  have h : x % ((4 : ℕ) : ℤ) = 1 ∨ x % ((4 : ℕ) : ℤ) = 3 := by push_cast; omega
  rw [← ZMod.intCast_mod x 4]
  rcases h with h | h <;> rw [h] <;> decide

/-! ### Item 2: `v_s(a² + δ² b²) ∈ {2, 3}` -/

/-- The residue check behind item 2: for `a₁, c₁` odd, `R = a₁² + 2a₂² + c₁² + 2c₂²` and
`I = 2a₁a₂ + 2c₁c₂` satisfy `R ≡ 2, I ≡ 0` or `R ≡ 0, I ≡ 2` modulo `4`. -/
theorem residue_check_sum_sq : ∀ a₁ a₂ c₁ c₂ : ZMod 4, (a₁ = 1 ∨ a₁ = 3) → (c₁ = 1 ∨ c₁ = 3) →
    (a₁ ^ 2 + 2 * a₂ ^ 2 + c₁ ^ 2 + 2 * c₂ ^ 2 = 2 ∧ 2 * a₁ * a₂ + 2 * c₁ * c₂ = 0) ∨
    (a₁ ^ 2 + 2 * a₂ ^ 2 + c₁ ^ 2 + 2 * c₂ ^ 2 = 0 ∧ 2 * a₁ * a₂ + 2 * c₁ * c₂ = 2) := by
  decide

/-- `v_s(a² + c²) ∈ {2, 3}` for `a, c ∈ ℤ[s]` prime to `s`. -/
theorem vS_sq_add_sq {a c : Zs} (ha : ¬ sqrt2Z ∣ a) (hc : ¬ sqrt2Z ∣ c) :
    vp sqrt2Z (Zs.toK0 (a ^ 2 + c ^ 2)) = 2 ∨ vp sqrt2Z (Zs.toK0 (a ^ 2 + c ^ 2)) = 3 := by
  rw [sqrt2Z_dvd_iff] at ha hc
  have hsum : a ^ 2 + c ^ 2 = ⟨a.re ^ 2 + 2 * a.im ^ 2 + c.re ^ 2 + 2 * c.im ^ 2,
      2 * a.re * a.im + 2 * c.re * c.im⟩ := by
    ext <;> simp [pow_two] <;> ring
  rw [hsum]
  rcases residue_check_sum_sq _ (a.im : ZMod 4) _ (c.im : ZMod 4) (odd_zmod_four ha)
    (odd_zmod_four hc) with ⟨hR, hI⟩ | ⟨hR, hI⟩
  · left; apply vS_mk_eq_two <;> push_cast <;> assumption
  · right; apply vS_mk_eq_three <;> push_cast <;> assumption

theorem not_sqrt2Z_dvd_deltaZ : ¬ sqrt2Z ∣ deltaZ := by
  rw [sqrt2Z_dvd_iff]; simp [deltaZ]

/-- Item 2: for `a, b ∈ ℤ[s]` with `s ∤ a` and `s ∤ b`, `v_s(a² + δ² b²) ∈ {2, 3}`. -/
theorem val_s_sq_add_delta_sq {a b : Zs} (ha : ¬ sqrt2Z ∣ a) (hb : ¬ sqrt2Z ∣ b) :
    vp sqrt2Z (Zs.toK0 (a ^ 2 + deltaZ ^ 2 * b ^ 2)) = 2 ∨
      vp sqrt2Z (Zs.toK0 (a ^ 2 + deltaZ ^ 2 * b ^ 2)) = 3 := by
  have hc : ¬ sqrt2Z ∣ deltaZ * b := fun h =>
    (prime_sqrt2Z.dvd_or_dvd h).elim not_sqrt2Z_dvd_deltaZ hb
  rw [← mul_pow]
  exact vS_sq_add_sq ha hc

/-! ### Item 1: rational `A, B` -/

theorem residue_check_rat_even : ∀ a b n : ZMod 4, (a = 1 ∨ a = 3) → (n = 1 ∨ n = 3) →
    (b = 0 ∨ b = 2) → a ^ 2 + 2 * b ^ 2 + n ^ 2 = 2 ∧ 2 * a * b = 0 := by
  decide

theorem residue_check_rat_odd : ∀ a b n : ZMod 4, (a = 1 ∨ a = 3) → (n = 1 ∨ n = 3) →
    (b = 1 ∨ b = 3) → a ^ 2 + 2 * b ^ 2 + n ^ 2 = 0 ∧ 2 * a * b = 2 := by
  decide

theorem even_zmod_four {x : ℤ} (hx : (2 : ℤ) ∣ x) : (x : ZMod 4) = 0 ∨ (x : ZMod 4) = 2 := by
  have h : x % ((4 : ℕ) : ℤ) = 0 ∨ x % ((4 : ℕ) : ℤ) = 2 := by push_cast; omega
  rw [← ZMod.intCast_mod x 4]
  rcases h with h | h <;> rw [h] <;> decide

/-- The integral form of item 1: for `a, n` odd, `v_s((a + b s)² + n²)` is `2` for `b` even and
`3` for `b` odd. -/
theorem vS_sq_add_odd_sq {a b n : ℤ} (ha : ¬ (2 : ℤ) ∣ a) (hn : ¬ (2 : ℤ) ∣ n) :
    ((2 : ℤ) ∣ b → vp sqrt2Z (Zs.toK0 ((⟨a, b⟩ : Zs) ^ 2 + (n : Zs) ^ 2)) = 2) ∧
    (¬ (2 : ℤ) ∣ b → vp sqrt2Z (Zs.toK0 ((⟨a, b⟩ : Zs) ^ 2 + (n : Zs) ^ 2)) = 3) := by
  have hsum : (⟨a, b⟩ : Zs) ^ 2 + (n : Zs) ^ 2 = ⟨a ^ 2 + 2 * b ^ 2 + n ^ 2, 2 * a * b⟩ := by
    ext <;> simp [pow_two] <;> ring
  rw [hsum]
  constructor
  · intro hb
    obtain ⟨hR, hI⟩ := residue_check_rat_even _ (b : ZMod 4) _ (odd_zmod_four ha)
      (odd_zmod_four hn) (even_zmod_four hb)
    apply vS_mk_eq_two <;> push_cast <;> assumption
  · intro hb
    obtain ⟨hR, hI⟩ := residue_check_rat_odd _ (b : ZMod 4) _ (odd_zmod_four ha)
      (odd_zmod_four hn) (odd_zmod_four hb)
    apply vS_mk_eq_three <;> push_cast <;> assumption

/-- `v₂(q) ≥ 0` (for `q ≠ 0`) iff the denominator of `q` is odd. -/
theorem padicValRat_nonneg_iff {q : ℚ} (hq : q ≠ 0) :
    0 ≤ padicValRat 2 q ↔ ¬ 2 ∣ q.den := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hcop := q.reduced
  rw [padicValRat_def]
  constructor
  · intro h hden
    have h2num : ¬ (2 : ℤ) ∣ q.num := by
      intro h2
      have h2' : 2 ∣ q.num.natAbs := Int.ofNat_dvd_left.mp h2
      have := Nat.dvd_gcd h2' hden
      rw [hcop.gcd_eq_one] at this; omega
    have h1 : padicValInt 2 q.num = 0 := padicValInt.eq_zero_of_not_dvd (by exact_mod_cast h2num)
    have h2 : 0 < padicValNat 2 q.den := by
      have : padicValNat 2 q.den ≠ 0 := by
        rw [Ne, padicValNat.eq_zero_iff, not_or, not_or, not_not]
        exact ⟨by norm_num, q.den_nz, hden⟩
      omega
    omega
  · intro hden
    rw [padicValNat.eq_zero_of_not_dvd hden]; simp

/-- For `q ≠ 0` with odd denominator: `v₂(q) ≥ 1` iff the numerator is even, and `v₂(q) = 0`
iff the numerator is odd. -/
theorem padicValRat_eq_zero_iff_of_den {q : ℚ} (hq : q ≠ 0) (hden : ¬ 2 ∣ q.den) :
    padicValRat 2 q = 0 ↔ ¬ (2 : ℤ) ∣ q.num := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hden, Nat.cast_zero, sub_zero,
    Nat.cast_eq_zero, padicValInt.eq_zero_iff]
  simp [hnum]

/-- Item 1: for `A, B ∈ ℚ` with `v₂(A) = 0`, `v₂(B) ≥ 0`:
`v_s((A + B s)² + 1) = 2` if `B = 0` or `v₂(B) ≥ 1`, and `= 3` if `B ≠ 0` and `v₂(B) = 0`. -/
theorem vS_sq_add_one (A B : ℚ) (hA : A ≠ 0) (hA2 : padicValRat 2 A = 0)
    (hB : B = 0 ∨ 0 ≤ padicValRat 2 B) :
    ((B = 0 ∨ 1 ≤ padicValRat 2 B) → vp sqrt2Z ((⟨A, B⟩ : K0) ^ 2 + 1) = 2) ∧
    ((B ≠ 0 ∧ padicValRat 2 B = 0) → vp sqrt2Z ((⟨A, B⟩ : K0) ^ 2 + 1) = 3) := by
  -- odd denominators
  have hAden : ¬ 2 ∣ A.den := (padicValRat_nonneg_iff hA).mp hA2.ge
  have hAnum : ¬ (2 : ℤ) ∣ A.num := (padicValRat_eq_zero_iff_of_den hA hAden).mp hA2
  have hBden : ¬ 2 ∣ B.den := by
    rcases hB with hB | hB
    · subst hB; simp
    · by_cases hB0 : B = 0
      · subst hB0; simp
      · exact (padicValRat_nonneg_iff hB0).mp hB
  -- common denominator `n = den A · den B`
  set n : ℤ := A.den * B.den with hn
  set a : ℤ := A.num * B.den with ha
  set b : ℤ := B.num * A.den with hb
  have hn2 : ¬ (2 : ℤ) ∣ n := by
    rw [hn, Int.prime_two.dvd_mul, not_or]
    exact ⟨by exact_mod_cast hAden, by exact_mod_cast hBden⟩
  have ha2 : ¬ (2 : ℤ) ∣ a := by
    rw [ha, Int.prime_two.dvd_mul, not_or]; exact ⟨hAnum, by exact_mod_cast hBden⟩
  have hb2 : (2 : ℤ) ∣ b ↔ (2 : ℤ) ∣ B.num := by
    rw [hb, Int.prime_two.dvd_mul]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd (by exact_mod_cast h) hAden
    · exact Or.inl
  have hnK : (n : K0) ≠ 0 := by
    rw [Int.cast_ne_zero]; intro h; rw [h] at hn2; simp at hn2
  -- `(A + B s)² + 1 = ((a + b s)² + n²) / n²`
  have hAB : (⟨A, B⟩ : K0) = Zs.toK0 ⟨a, b⟩ / (n : K0) := by
    rw [eq_div_iff hnK]
    have e1 : A * A.den = A.num := Rat.mul_den_eq_num A
    have e2 : B * B.den = B.num := Rat.mul_den_eq_num B
    ext
    · simp [ha, hn]; linear_combination (B.den : ℚ) * e1
    · simp [hb, hn]; linear_combination (A.den : ℚ) * e2
  have hexpr : (⟨A, B⟩ : K0) ^ 2 + 1 =
      Zs.toK0 ((⟨a, b⟩ : Zs) ^ 2 + (n : Zs) ^ 2) / (n : K0) ^ 2 := by
    rw [hAB, map_add, map_pow, map_pow, toK0_intCast]; field_simp
  have hnum0 : Zs.toK0 ((⟨a, b⟩ : Zs) ^ 2 + (n : Zs) ^ 2) ≠ 0 := by
    intro h
    have h' : (⟨A, B⟩ : K0) ^ 2 + 1 = 0 := by rw [hexpr, h, zero_div]
    -- `(A + B s)² = -1` is impossible: compare the `re` parts after taking norms
    have hre := congrArg QuadraticAlgebra.re h'
    simp [pow_two] at hre
    nlinarith [mul_self_nonneg A, mul_self_nonneg B]
  have hvn : vp sqrt2Z ((n : K0) ^ 2) = 0 := by
    have hnZ : (n : Zs) ≠ 0 := by
      intro h; apply hnK; rw [← toK0_intCast, h, map_zero]
    have : vp sqrt2Z (Zs.toK0 (n : Zs)) = 0 := by
      rw [vp_eq_zero_iff prime_sqrt2Z hnZ, sqrt2Z_dvd_iff]; simpa using hn2
    rw [vp_pow prime_sqrt2Z, ← toK0_intCast, this, mul_zero]
  rw [hexpr, vp_div prime_sqrt2Z hnum0 (pow_ne_zero _ hnK), hvn, sub_zero]
  obtain ⟨h1, h2⟩ := vS_sq_add_odd_sq (b := b) ha2 hn2
  constructor
  · intro h
    apply h1
    rw [hb2]
    rcases h with h | h
    · subst h; simp
    · by_contra hodd
      have hB0 : B ≠ 0 := by rintro rfl; simp at hodd
      have := (padicValRat_eq_zero_iff_of_den hB0 hBden).mpr hodd
      omega
  · rintro ⟨hB0, hv⟩
    apply h2
    rw [hb2]
    exact (padicValRat_eq_zero_iff_of_den hB0 hBden).mp hv

end ZInQ
