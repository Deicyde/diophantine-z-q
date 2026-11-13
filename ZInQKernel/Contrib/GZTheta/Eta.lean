import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# gz-theta: the multiplier of `η²` under `SL(2, ℤ)`, by the Euclidean algorithm

For `γ = (a b; c d) ∈ SL(2, ℤ)` and `Im z > 0`:

  `η(γ z)² = ζ^{φ(a,b,c,d)} (c z + d) η(z)²`,  `ζ = e^{π i / 6}`,

where the exponent `φ` is computed by the Euclidean algorithm on `(a, c)`
(`etaSqExp`, structural recursion on a fuel argument, so that the kernel evaluates it on
numerals). Only the two generator laws of Mathlib's `η` are used:
`η(z + 1) = e^{π i/12} η(z)` and `η(−1/z) = (√i)⁻¹ √z η(z)` (`eta_comp_eq_csqrt_I_inv`).
`η²` has weight 1, so no square root enters the multiplier.
-/

open Complex ModularForm
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace ZInQ.GZTheta

/-- `ζ = e^{π i / 6}`, a primitive 12th root of unity. -/
def zeta12 : ℂ := cexp (π * I / 6)

theorem zeta12_ne_zero : zeta12 ≠ 0 := Complex.exp_ne_zero _

theorem zeta12_zpow (n : ℤ) : zeta12 ^ n = cexp (n * (π * I / 6)) := by
  rw [zeta12, ← Complex.exp_int_mul]

theorem zeta12_pow_twelve : zeta12 ^ (12 : ℤ) = 1 := by
  rw [zeta12_zpow]
  have : ((12 : ℤ) : ℂ) * (π * I / 6) = 2 * π * I := by push_cast; ring
  rw [this, Complex.exp_two_pi_mul_I]

theorem zeta12_zpow_neg_three : zeta12 ^ (-3 : ℤ) = -I := by
  rw [zeta12_zpow]
  have : ((-3 : ℤ) : ℂ) * (π * I / 6) = -(π / 2 * I) := by push_cast; ring
  rw [this, Complex.exp_neg, Complex.exp_mul_I]
  rw [show (π : ℂ) / 2 = ((π / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem zeta12_zpow_six : zeta12 ^ (6 : ℤ) = -1 := by
  rw [zeta12_zpow]
  have : ((6 : ℤ) : ℂ) * (π * I / 6) = π * I := by push_cast; ring
  rw [this, Complex.exp_pi_mul_I]

theorem zeta12_zpow_emod (n : ℤ) : zeta12 ^ n = zeta12 ^ (n % 12) := by
  conv_lhs => rw [← Int.emod_add_ediv_mul n 12]
  rw [zpow_add₀ zeta12_ne_zero, mul_comm (n / 12), zpow_mul, zeta12_pow_twelve, one_zpow, mul_one]

/-! ### The two generator laws for `η²` -/

/-- **Translation law**: `η(z + n)² = ζⁿ η(z)²` for every integer `n`. -/
theorem eta_sq_add_intCast (z : ℂ) (n : ℤ) : η (z + n) ^ 2 = zeta12 ^ n * η z ^ 2 := by
  have hq (m : ℕ) : eta_q m (z + n) = eta_q m z := by
    have harg : 2 * π * I * (m + 1) * (z + n) =
        2 * π * I * (m + 1) * z + ((m + 1) * n : ℤ) * (2 * π * I) := by
      push_cast
      ring
    simp only [eta_q_eq_cexp]
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hexp : Function.Periodic.qParam 24 (z + n) =
      cexp (π * I * n / 12) * Function.Periodic.qParam 24 z := by
    simp only [Function.Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h1 : η (z + n) = cexp (π * I * n / 12) * η z := by
    simp only [ModularForm.eta, hq, hexp, mul_assoc]
  rw [h1, mul_pow, zeta12_zpow, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem sqrt_sq_eq (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  have := Complex.cpow_nat_inv_pow w (n := 2) two_ne_zero
  rw [Complex.sqrt]
  exact_mod_cast this

/-- **Inversion law**: `η(−1/z)² = −i z η(z)²` for `Im z > 0`. -/
theorem eta_sq_neg_inv {z : ℂ} (hz : 0 < z.im) : η (-1 / z) ^ 2 = -I * z * η z ^ 2 := by
  have h := eta_comp_eq_csqrt_I_inv (show z ∈ upperHalfPlaneSet from hz)
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  rw [h, mul_pow, mul_pow, inv_pow, sqrt_sq_eq I, sqrt_sq_eq z, Complex.inv_I]
  ring


/-! ### Möbius maps with integer entries -/

theorem mobius_denom_ne_zero {a b c d : ℤ} (h : a * d - b * c = 1) {z : ℂ} (hz : 0 < z.im) :
    (c : ℂ) * z + d ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, zero_im] at him
  have hc : (c : ℝ) = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · exact h1
    · exact absurd h1 hz.ne'
  have hc' : c = 0 := by exact_mod_cast hc
  subst hc'
  have hre := congrArg Complex.re h0
  simp only [Int.cast_zero, zero_mul, zero_add, intCast_re, zero_re] at hre
  have hd : d = 0 := by exact_mod_cast hre
  subst hd
  simp at h

theorem mobius_im_pos {a b c d : ℤ} (h : a * d - b * c = 1) {z : ℂ} (hz : 0 < z.im) :
    0 < (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).im := by
  let g : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩
  have := (g • (⟨z, hz⟩ : ℍ)).im_pos
  rw [UpperHalfPlane.im, coe_specialLinearGroup_apply] at this
  simpa [g] using this

/-! ### The Euclidean exponent -/

/-- The exponent of the multiplier of `η²`, by the Euclidean algorithm with fuel. For
`γ = (a b; c d)` with `c ≠ 0`, `γ = T^q S γ₃` with `q = ⌊a / c⌋` and
`γ₃ = (c, d; −(a mod c), −(b − q d))`. -/
def etaSqExp : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ
  | 0, a, b, _, _ => if a = 1 then b else 6 - b
  | fuel + 1, a, b, c, d =>
    if c = 0 then (if a = 1 then b else 6 - b)
    else a / c - 3 + etaSqExp fuel c d (-(a % c)) (-(b - a / c * d))

/-- **The multiplier of `η²`.** For integers `a d − b c = 1`, `|c| ≤ fuel`, and `Im z > 0`:
`η((a z + b)/(c z + d))² = ζ^{etaSqExp fuel a b c d} (c z + d) η(z)²`. -/
theorem eta_sq_mobius : ∀ (fuel : ℕ) (a b c d : ℤ), c.natAbs ≤ fuel → a * d - b * c = 1 →
    ∀ z : ℂ, 0 < z.im →
      η (((a : ℂ) * z + b) / ((c : ℂ) * z + d)) ^ 2 =
        zeta12 ^ (etaSqExp fuel a b c d) * ((c : ℂ) * z + d) * η z ^ 2 := by
  -- the case `c = 0`
  have base : ∀ (a b c d : ℤ), c = 0 → a * d - b * c = 1 → ∀ z : ℂ,
      η (((a : ℂ) * z + b) / ((c : ℂ) * z + d)) ^ 2 =
        zeta12 ^ (if a = 1 then b else 6 - b) * ((c : ℂ) * z + d) * η z ^ 2 := by
    intro a b c d hc h z
    subst hc
    have had : a * d = 1 := by simpa using h
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [Int.cast_one, one_mul, Int.cast_zero, zero_mul, zero_add, div_one, ite_true,
        mul_one]
      exact eta_sq_add_intCast z b
    · have e : ((((-1 : ℤ) : ℂ) * z + b) / (((0 : ℤ) : ℂ) * z + ((-1 : ℤ) : ℂ))) =
          z + ((-b : ℤ) : ℂ) := by push_cast; field_simp; ring
      rw [e, eta_sq_add_intCast, if_neg (by decide), zpow_sub₀ zeta12_ne_zero, zeta12_zpow_six,
        zpow_neg]
      push_cast
      field_simp
      ring
  intro fuel
  induction fuel with
  | zero =>
    intro a b c d hc h z _
    have : c = 0 := by omega
    exact base a b c d this h z
  | succ n ih =>
    intro a b c d hc h z hz
    by_cases hc0 : c = 0
    · simp only [etaSqExp, if_pos hc0]
      exact base a b c d hc0 h z
    simp only [etaSqExp, if_neg hc0]
    set q := a / c with hq
    set r := a % c with hr
    set b' := b - q * d with hb'
    have hqr : c * q + r = a := Int.mul_ediv_add_emod a c
    have hr0 : 0 ≤ r := Int.emod_nonneg a hc0
    have hrc : r < (c.natAbs : ℤ) := Int.emod_lt a hc0
    have hdet3 : c * -b' - d * -r = 1 := by
      rw [hb']; rw [← hqr] at h; linear_combination h
    have hc3 : (-r).natAbs ≤ n := by
      omega
    -- `w₃ = (c z + d) / (−r z − b')`
    have hD := mobius_denom_ne_zero h hz
    have hD3 := mobius_denom_ne_zero hdet3 hz
    have hw3 := mobius_im_pos hdet3 hz
    set w3 : ℂ := ((c : ℂ) * z + d) / (((-r : ℤ) : ℂ) * z + ((-b' : ℤ) : ℂ)) with hw3def
    have hsplit : ((a : ℂ) * z + b) / ((c : ℂ) * z + d) = -1 / w3 + (q : ℂ) := by
      rw [hw3def]
      have hD3' : -((r : ℂ) * z) - (b' : ℂ) ≠ 0 := by
        have := hD3; push_cast at this; rw [show -(r : ℂ) * z + -(b' : ℂ) = -((r : ℂ) * z) - b' by ring] at this
        exact this
      push_cast
      rw [← hqr, hb']
      push_cast
      field_simp
      ring
    rw [hsplit, eta_sq_add_intCast, eta_sq_neg_inv hw3,
      ih c d (-r) (-b') hc3 hdet3 z hz]
    have hprod : w3 * (((-r : ℤ) : ℂ) * z + ((-b' : ℤ) : ℂ)) = (c : ℂ) * z + d := by
      rw [hw3def]; exact div_mul_cancel₀ _ hD3
    rw [show (q : ℤ) - 3 + etaSqExp n c d (-r) (-b') = q + (-3) + etaSqExp n c d (-r) (-b') by ring,
      zpow_add₀ zeta12_ne_zero, zpow_add₀ zeta12_ne_zero, zeta12_zpow_neg_three, ← hprod]
    ring

end ZInQ.GZTheta
