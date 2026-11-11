import ZInQKernel.Hypotheses.Height

/-!
# wk-h, Tier 1: the return to `u` (N5 F4 and the final numerics) in Lean

Draft for the reduction plan `docs/research/wk-h.md` §4.1. It replaces `SixContactMin` by its
`j`-form `JHeightBound`: a bound on the height of the Hauptmodul value `J(u) = −57600F(u)²/G(u)⁶`
(N5 L949-964; `scratch/h-b1/b1_checks.py`). The step from `J(u)` back to `u` (N5's rational-root
argument, F4 of `h-trust.md`) and the final arithmetic become Lean proofs.

`JHeightBound` is *not* a published theorem: it is the composite of h-trust steps A1-F3. This tier
only removes F4 and the final numerics from the trust base and fixes the interface for Tier 2
(`scratch/wk-h/Arakelov.lean`), whose conclusion is `JHeightBound`.

The constant `40·10⁴·2²⁴ + 22` is N5's: `h(j) ≤ 40 h([z_m]) + 22` (F2) with
`h([z_m]) ≤ 10⁴·2²⁴·max(1, h_F(A))` (F3), and `max(1, h_F(A)) ≤ max(1, C_cm, Q¹⁷) M²⁴` (E4).
-/

namespace ZInQ.WkH

open ZInQ

/-- The binary sextic `F_h(a,b) = a(a+15b)(a+20b)(a+24b)(a+30b)(a+60b)`. -/
def Fh (a b : ℤ) : ℤ := a * (a + 15 * b) * (a + 20 * b) * (a + 24 * b) * (a + 30 * b) * (a + 60 * b)

/-- The binary quadratic `G_h(a,b) = 7a² + 300ab + 3600b²` (discriminant `−10800 < 0`). -/
def Gh (a b : ℤ) : ℤ := 7 * a ^ 2 + 300 * a * b + 3600 * b ^ 2

/-- The Hauptmodul value `J(u) = −57600 F(u)² / G(u)⁶` (h-b1 M7). -/
def Jmap (u : ℚ) : ℚ :=
  -57600 * (u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)) ^ 2 /
    (7 * u ^ 2 + 300 * u + 3600) ^ 6

/-- Nullstellensatz certificate for `x⁷` (`scratch/wk-h/f4_cert.py`). -/
theorem cert_x (a b : ℤ) :
    3 * a ^ 7 = (-200 * a - 4800 * b) * Fh a b +
      (29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 + 2880000 * a ^ 2 * b ^ 3 +
        17280000 * a * b ^ 4) * Gh a b := by
  unfold Fh Gh; ring

/-- Nullstellensatz certificate for `y⁷` (`scratch/wk-h/f4_cert.py`). -/
theorem cert_y (a b : ℤ) :
    104976000000 * b ^ 7 = (-1001 * a - 37650 * b) * Fh a b +
      (143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2 + 20691900 * a ^ 2 * b ^ 3 +
        133110000 * a * b ^ 4 + 29160000 * b ^ 5) * Gh a b := by
  unfold Fh Gh; ring

/-- `G` has no rational zero (negative discriminant). -/
theorem G_ne_zero (u : ℚ) : 7 * u ^ 2 + 300 * u + 3600 ≠ 0 := by
  nlinarith [sq_nonneg (7 * u + 150)]

/-- `C₀ = 57600²·3⁷·(2¹⁰3⁸5⁶)⁷`, the bound for the cancellation in `J(u)`. -/
def C0 : ℤ := (57600 * 3 ^ 7) * (57600 * 104976000000 ^ 7)

/-- **Cancellation bound.** For coprime `a, b`, a common divisor of `57600F_h²` and `G_h⁶` divides
`C₀` (from `cert_x`, `cert_y` raised to the 7th power). -/
theorem dvd_C0 {a b c : ℤ} (hab : IsCoprime a b) (hP : c ∣ 57600 * Fh a b ^ 2)
    (hQ : c ∣ Gh a b ^ 6) : c ∣ C0 := by
  have key : ∀ x y : ℤ, 57600 * (x + y) ^ 7 =
      57600 * x ^ 2 * (x ^ 5 + 7 * x ^ 4 * y + 21 * x ^ 3 * y ^ 2 + 35 * x ^ 2 * y ^ 3 +
        35 * x * y ^ 4 + 21 * y ^ 5) + y ^ 6 * (57600 * (7 * x + y)) := by intros; ring
  have hsplit : ∀ (A B : ℤ), c ∣ 57600 * (A * Fh a b + B * Gh a b) ^ 7 := by
    intro A B
    rw [key]
    refine dvd_add ?_ ?_
    · have : 57600 * (A * Fh a b) ^ 2 = (57600 * Fh a b ^ 2) * A ^ 2 := by ring
      rw [this, mul_assoc]; exact dvd_mul_of_dvd_left hP _
    · have : (B * Gh a b) ^ 6 = Gh a b ^ 6 * B ^ 6 := by ring
      rw [this, mul_assoc]; exact dvd_mul_of_dvd_left hQ _
  have hx : c ∣ 57600 * 3 ^ 7 * a ^ 49 := by
    have e : 57600 * 3 ^ 7 * a ^ 49 = 57600 * (3 * a ^ 7) ^ 7 := by ring
    rw [e, cert_x]; exact hsplit _ _
  have hy : c ∣ 57600 * 104976000000 ^ 7 * b ^ 49 := by
    have e : 57600 * 104976000000 ^ 7 * b ^ 49 = 57600 * (104976000000 * b ^ 7) ^ 7 := by ring
    rw [e, cert_y]; exact hsplit _ _
  obtain ⟨s, t, hst⟩ := hab.pow (m := 49) (n := 49)
  have e : C0 = (57600 * 104976000000 ^ 7 * s) * (57600 * 3 ^ 7 * a ^ 49) +
      (57600 * 3 ^ 7 * t) * (57600 * 104976000000 ^ 7 * b ^ 49) := by
    have : C0 = C0 * (s * a ^ 49 + t * b ^ 49) := by rw [hst, mul_one]
    rw [this, C0]; ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right hy _)

theorem abs_monomial_le {a b m : ℤ} (ha : |a| ≤ m) (hb : |b| ≤ m) (i j : ℕ) :
    |a ^ i * b ^ j| ≤ m ^ (i + j) := by
  have hm : 0 ≤ m := (abs_nonneg a).trans ha
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ha _) (pow_le_pow_left₀ (abs_nonneg _) hb _)
    (by positivity) (by positivity)

/-- **Lower bound.** With `m = max(|a|, |b|) > 0`: `m¹² ≤ 10⁴⁸ max(57600F_h², G_h⁶)`. -/
theorem lower_bound {a b m : ℤ} (ha : |a| ≤ m) (hb : |b| ≤ m) (hm : 0 < m)
    (hmax : m = |a| ∨ m = |b|) :
    m ^ 12 ≤ 10 ^ 48 * max (57600 * Fh a b ^ 2) (Gh a b ^ 6) := by
  by_contra hlt
  push Not at hlt
  have hP := le_max_left (57600 * Fh a b ^ 2) (Gh a b ^ 6)
  have hQ := le_max_right (57600 * Fh a b ^ 2) (Gh a b ^ 6)
  have hF : 240 * 10 ^ 24 * |Fh a b| < m ^ 6 := by
    have h2 : (240 * 10 ^ 24 * |Fh a b|) ^ 2 < (m ^ 6) ^ 2 := by
      rw [mul_pow, sq_abs]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  have hG : 10 ^ 8 * |Gh a b| < m ^ 2 := by
    have h6 : (10 ^ 8 * |Gh a b|) ^ 6 < (m ^ 2) ^ 6 := by
      rw [mul_pow, pow_abs, abs_of_nonneg (by positivity : (0:ℤ) ≤ Gh a b ^ 6)]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 6 (by positivity) h6
  have hX : 240 * 10 ^ 24 * (m * |Fh a b|) < m ^ 7 := by nlinarith
  have hY : 10 ^ 8 * (m ^ 5 * |Gh a b|) < m ^ 7 := by
    have : (0 : ℤ) < m ^ 5 := by positivity
    nlinarith
  have m10 : -m ≤ a ∧ a ≤ m := abs_le.mp ha
  have m01 : -m ≤ b ∧ b ≤ m := abs_le.mp hb
  have mono : ∀ i j : ℕ, i + j = 5 → -m ^ 5 ≤ a ^ i * b ^ j ∧ a ^ i * b ^ j ≤ m ^ 5 := by
    intro i j hij
    have := abs_monomial_le ha hb i j
    rw [hij] at this
    exact abs_le.mp this
  have m50 := mono 5 0 rfl
  have m41 := mono 4 1 rfl
  have m32 := mono 3 2 rfl
  have m23 := mono 2 3 rfl
  have m14 := mono 1 4 rfl
  have m05 := mono 0 5 rfl
  simp only [pow_one, pow_zero, mul_one, one_mul] at m50 m41 m32 m23 m14 m05
  have hm7 : (0 : ℤ) < m ^ 7 := by positivity
  have tri : ∀ A B : ℤ, |A * Fh a b + B * Gh a b| ≤ |A| * |Fh a b| + |B| * |Gh a b| := by
    intro A B; rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
  rcases hmax with h | h
  · have hA : |-200 * a - 4800 * b| ≤ 5000 * m := by
      rw [abs_le]; constructor <;> linarith
    have hB : |29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 + 2880000 * a ^ 2 * b ^ 3 +
        17280000 * a * b ^ 4| ≤ 20328129 * m ^ 5 := by
      rw [abs_le]; constructor <;> linarith
    have e := tri (-200 * a - 4800 * b) (29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 +
      2880000 * a ^ 2 * b ^ 3 + 17280000 * a * b ^ 4)
    rw [← cert_x, abs_mul, abs_pow, ← h, show |(3 : ℤ)| = 3 by norm_num] at e
    have e1 := mul_le_mul_of_nonneg_right hA (abs_nonneg (Fh a b))
    have e2 := mul_le_mul_of_nonneg_right hB (abs_nonneg (Gh a b))
    linarith
  · have hA : |-1001 * a - 37650 * b| ≤ 38651 * m := by
      rw [abs_le]; constructor <;> linarith
    have hB : |143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2 +
        20691900 * a ^ 2 * b ^ 3 + 133110000 * a * b ^ 4 + 29160000 * b ^ 5| ≤
        184009200 * m ^ 5 := by
      rw [abs_le]; constructor <;> linarith
    have e := tri (-1001 * a - 37650 * b) (143 * a ^ 5 + 20557 * a ^ 4 * b +
      1026600 * a ^ 3 * b ^ 2 + 20691900 * a ^ 2 * b ^ 3 + 133110000 * a * b ^ 4 + 29160000 * b ^ 5)
    rw [← cert_y, abs_mul, abs_pow, ← h, show |(104976000000 : ℤ)| = 104976000000 by norm_num] at e
    have e1 := mul_le_mul_of_nonneg_right hA (abs_nonneg (Fh a b))
    have e2 := mul_le_mul_of_nonneg_right hB (abs_nonneg (Gh a b))
    linarith

/-- **F4, strengthened.** `12 h(u) ≤ h(J(u)) + 450` for `u ∉ 𝒞` (N5: `h(u) < h(J(u)) + 74`). -/
theorem twelve_mul_ratHeight_le (u : ℚ) (hu : u ∉ contactSet) :
    12 * ratHeight u ≤ ratHeight (Jmap u) + 450 := by
  sorry

/-- `SixContactMin` for a general prime set `S` (`ZInQ.SixContactMin` is `SixContactMinAt
Mult.S_mul` by `rfl`; this scratch file imports only `Hypotheses/Height.lean`, because the
upstream package `lean/` is not built in this worktree). -/
def SixContactMinAt (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet → ratHeight u ≤ heightH6 (heightD : ℝ) * (contactSupport S u : ℝ) ^ 24

theorem contactSupport_pos' (S : Finset ℕ) (u : ℚ) : 0 < contactSupport S u := by
  unfold contactSupport
  exact Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

/-- The constant `X(R) = max(1, C_cm, Q_R¹⁷)` of N5's final display. -/
noncomputable def heightX (R : ℝ) : ℝ := max 1 (max (heightCcm : ℝ) (heightQ R ^ 17))

/-- **The `j`-form of H** (residual hypothesis of Tier 1): for every `u ∈ ℚ \ 𝒞`,
`h(J(u)) ≤ (40·10⁴·2²⁴ + 22)·max(1, C_cm, Q_D¹⁷)·M_S(u)²⁴`, at `S = Mult.S_mul`. -/
def JHeightBound (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ratHeight (Jmap u) ≤
      (40 * 10000 * 2 ^ 24 + 22 : ℝ) * heightX heightD * (contactSupport S u : ℝ) ^ 24

theorem heightH6_eq (R : ℝ) : heightH6 R = 2 * 10 ^ 13 * heightX R := rfl

/-- **Tier-1 reduction.** `JHeightBound → SixContactMin` (F4 and the final numerics). -/
theorem sixContactMin_of_jHeightBound {S : Finset ℕ} (hJ : JHeightBound S) :
    SixContactMinAt S := by
  intro u hu
  have h12 := twelve_mul_ratHeight_le u hu
  have hj := hJ u hu
  have hX : 1 ≤ heightX heightD := le_max_left _ _
  have hM : (1 : ℝ) ≤ (contactSupport S u : ℝ) ^ 24 :=
    one_le_pow₀ (by exact_mod_cast contactSupport_pos' _ _)
  have hXM : 1 ≤ heightX heightD * (contactSupport S u : ℝ) ^ 24 :=
    one_le_mul_of_one_le_of_one_le hX hM
  rw [heightH6_eq]
  nlinarith

end ZInQ.WkH
