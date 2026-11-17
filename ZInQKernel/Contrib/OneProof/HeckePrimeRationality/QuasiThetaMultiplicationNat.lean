import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.QuasiThetaMultiplicationTwo
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Multiplication for every positive division degree

All theta hypotheses are explicit. The analytic cancellation and elliptic
boundedness arguments are reused from the two-division theorem.
-/

noncomputable section

open Complex Set Filter Function Finset
open scoped Topology Real BigOperators

namespace QuasiThetaMultiplicationNat

local notation "κ" => ((Real.pi : ℂ) * Complex.I)

/-- The translate indexed by the two division coordinates. -/
def shift (n : ℕ) (τ : UpperHalfPlane) (r s : Fin n) : ℂ :=
  ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (n : ℂ)

/-- The actual product of all `n²` translates. -/
def numerator (n : ℕ) (τ : UpperHalfPlane) (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∏ r : Fin n, ∏ s : Fin n, H (z + shift n τ r s)

/-- The scaled function and the compensating phase. Natural subtraction is
used only for `n - 1`; all substantive theorems require `0 < n`. -/
def denominator (n : ℕ) (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * z) * H ((n : ℂ) * z)

lemma cast_ne_zero {n : ℕ} (hn : 0 < n) : (n : ℂ) ≠ 0 := by
  exact_mod_cast hn.ne'

lemma cast_pred {n : ℕ} (hn : 0 < n) : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
  rw [Nat.cast_sub (by omega), Nat.cast_one]

lemma differentiable_numerator {n : ℕ} {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) : Differentiable ℂ (numerator n τ H) := by
  unfold numerator
  fun_prop

lemma differentiable_denominator {n : ℕ} {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) : Differentiable ℂ (denominator n H) := by
  unfold denominator
  fun_prop

lemma numerator_zero_iff_factor (n : ℕ) (τ : UpperHalfPlane) (H : ℂ → ℂ) (z : ℂ) :
    numerator n τ H z = 0 ↔ ∃ r s : Fin n, H (z + shift n τ r s) = 0 := by
  simp only [numerator, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]

lemma denominator_zero_iff {n : ℕ} {H : ℂ → ℂ} (z : ℂ) :
    denominator n H z = 0 ↔ H ((n : ℂ) * z) = 0 := by
  simp [denominator, Complex.exp_ne_zero]

/-- Positive shifts require the residues of the negative lattice
coefficients. Integer residues are taken before conversion to naturals. -/
theorem numerator_zero_iff_denominator_zero {n : ℕ} {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hn : 0 < n)
    (hzeros : ∀ z, H z = 0 ↔ ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * (τ : ℂ))
    (z : ℂ) : numerator n τ H z = 0 ↔ denominator n H z = 0 := by
  have hnC := cast_ne_zero hn
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  rw [numerator_zero_iff_factor, denominator_zero_iff, hzeros]
  constructor
  · rintro ⟨r, s, hrs⟩
    obtain ⟨a, b, hab⟩ := (hzeros _).mp hrs
    refine ⟨(n : ℤ) * a - (s : ℕ), (n : ℤ) * b - (r : ℕ), ?_⟩
    unfold shift at hab
    push_cast
    field_simp [hnC] at hab
    linear_combination hab
  · rintro ⟨a, b, hab⟩
    have ha : (-a) / (n : ℤ) * (n : ℤ) + (-a) % (n : ℤ) = -a :=
      Int.ediv_mul_add_emod (-a) n
    have hb : (-b) / (n : ℤ) * (n : ℤ) + (-b) % (n : ℤ) = -b :=
      Int.ediv_mul_add_emod (-b) n
    have ha0 := Int.emod_nonneg (-a) hnZ.ne'
    have hb0 := Int.emod_nonneg (-b) hnZ.ne'
    have han := Int.emod_lt_of_pos (-a) hnZ
    have hbn := Int.emod_lt_of_pos (-b) hnZ
    let r : Fin n := ⟨((-b) % (n : ℤ)).toNat, by omega⟩
    let s : Fin n := ⟨((-a) % (n : ℤ)).toNat, by omega⟩
    have hr : ((r : ℕ) : ℤ) = (-b) % (n : ℤ) := by
      dsimp [r]
      exact Int.toNat_of_nonneg hb0
    have hs : ((s : ℕ) : ℤ) = (-a) % (n : ℤ) := by
      dsimp [s]
      exact Int.toNat_of_nonneg ha0
    have hrc : (r : ℂ) = (((-b) % (n : ℤ) : ℤ) : ℂ) := by exact_mod_cast hr
    have hsc : (s : ℂ) = (((-a) % (n : ℤ) : ℤ) : ℂ) := by exact_mod_cast hs
    have hac : (((-a) / (n : ℤ) : ℤ) : ℂ) * (n : ℂ) +
        (((-a) % (n : ℤ) : ℤ) : ℂ) = -(a : ℂ) := by exact_mod_cast ha
    have hbc : (((-b) / (n : ℤ) : ℤ) : ℂ) * (n : ℂ) +
        (((-b) % (n : ℤ) : ℤ) : ℂ) = -(b : ℂ) := by exact_mod_cast hb
    refine ⟨r, s, (hzeros _).mpr ⟨-((-a) / (n : ℤ)), -((-b) / (n : ℤ)), ?_⟩⟩
    unfold shift
    push_cast
    rw [hrc, hsc]
    apply (mul_left_inj' hnC).mp
    field_simp [hnC]
    linear_combination hab + hac + (τ : ℂ) * hbc

/-- The origin's actual nonzero derivative propagates to the scaled
function's zeros, with the positive degree providing the extra factor. -/
theorem denominator_deriv_ne_zero_at_zero {n : ℕ} {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hn : 0 < n) (hH : Differentiable ℂ H)
    (h1 : ∀ z, H (z + 1) = -H z)
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z)
    (hzeros : ∀ z, H z = 0 ↔ ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * (τ : ℂ))
    (hd0 : deriv H 0 ≠ 0) {z : ℂ} (hz : denominator n H z = 0) :
    deriv (denominator n H) z ≠ 0 := by
  have hHz := (denominator_zero_iff z).mp hz
  have hdH := QuasiThetaMultiplicationTwo.deriv_ne_zero_at_zero hH h1 hτ hzeros hd0 hHz
  have hlin : HasDerivAt (fun w : ℂ => (n : ℂ) * w) (n : ℂ) z := by
    simpa using! ((hasDerivAt_id z).const_mul (n : ℂ))
  have hscale : HasDerivAt (fun w : ℂ => H ((n : ℂ) * w))
      (deriv H ((n : ℂ) * z) * (n : ℂ)) z := by
    simpa only [Function.comp_def] using! (hH ((n : ℂ) * z)).hasDerivAt.comp z hlin
  have he : HasDerivAt (fun w : ℂ => Complex.exp (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * w))
      (Complex.exp (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * z) *
        (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ))) z := by
    simpa using! ((hasDerivAt_id z).const_mul (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ))).cexp
  have hd : deriv (denominator n H) z =
      (Complex.exp (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * z) *
        (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ))) * H ((n : ℂ) * z) +
        Complex.exp (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * z) *
          (deriv H ((n : ℂ) * z) * (n : ℂ)) := by
    simpa only [denominator, Pi.mul_apply] using! (he.mul hscale).deriv
  rw [hd, hHz, mul_zero, zero_add]
  exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero hdH (cast_ne_zero hn))

/-- Gauss' sum over the actual division indices, in the complex field. -/
lemma sum_indices (n : ℕ) :
    (∑ r : Fin n, (r : ℂ)) = (n : ℂ) * ((n - 1 : ℕ) : ℂ) / 2 := by
  have hnat : (∑ r : Fin n, (r : ℕ)) * 2 = n * (n - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n]
    exact Finset.sum_range_id_mul_two n
  have hcast : (∑ r : Fin n, (r : ℂ)) * 2 = (n : ℂ) * ((n - 1 : ℕ) : ℂ) := by
    exact_mod_cast hnat
  linear_combination (1 / 2 : ℂ) * hcast

/-- The total displacement of the `n²` actual translates. -/
lemma sum_shifts {n : ℕ} (hn : 0 < n) (τ : UpperHalfPlane) :
    (∑ r : Fin n, ∑ s : Fin n, shift n τ r s) =
      ((n : ℂ) * ((n - 1 : ℕ) : ℂ) / 2) * ((τ : ℂ) + 1) := by
  have hnC := cast_ne_zero hn
  calc
    _ = ((n : ℂ) * ((∑ r : Fin n, (r : ℂ)) * (τ : ℂ)) +
        (n : ℂ) * (∑ s : Fin n, (s : ℂ))) / (n : ℂ) := by
      simp_rw [shift, ← Finset.sum_div, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.sum_mul]
    _ = (∑ r : Fin n, (r : ℂ)) * ((τ : ℂ) + 1) := by
      field_simp [hnC]
    _ = _ := by rw [sum_indices]

/-- The constant phase disappears because its integer coefficient is even. -/
lemma exp_even_pi_I (m : ℕ) (hm : Even m) : Complex.exp (-κ * (m : ℂ)) = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have he : -κ * ((k + k : ℕ) : ℂ) = (-(k : ℤ) : ℂ) * (2 * κ) := by
    push_cast
    ring
  rw [he]
  simpa only [zero_add, Complex.exp_zero, Int.cast_neg] using
    QuasiThetaMultiplicationTwo.exp_add_int_two_pi_I 0 (-(k : ℤ))

lemma exp_degree_phase (n : ℕ) :
    Complex.exp (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ)) = 1 := by
  have he := exp_even_pi_I (n * (n - 1)) (Nat.even_mul_pred_self n)
  simpa only [Nat.cast_mul, mul_assoc] using he

lemma sign_square (n : ℕ) : (-1 : ℂ) ^ (n * n) = (-1 : ℂ) ^ n := by
  rw [neg_one_pow_eq_pow_mod_two (n * n), neg_one_pow_eq_pow_mod_two n]
  congr 1
  rw [Nat.mul_mod]
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hn with hn | hn <;> simp [hn]

lemma numerator_one (τ : UpperHalfPlane) (H : ℂ → ℂ) (z : ℂ) :
    numerator 1 τ H z = H z := by
  simp [numerator, shift]

lemma denominator_one (H : ℂ → ℂ) (z : ℂ) : denominator 1 H z = H z := by
  simp [denominator]

/-- Repeated translation by the real period. -/
lemma quasi_add_nat_one {H : ℂ → ℂ} (h1 : ∀ z, H (z + 1) = -H z)
    (m : ℕ) (z : ℂ) : H (z + (m : ℂ)) = (-1 : ℂ) ^ m * H z := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show z + ((m + 1 : ℕ) : ℂ) = (z + (m : ℂ)) + 1 by push_cast; ring, h1, ih]
    rw [pow_succ]
    ring

/-- Iterating the τ quasi-period retains the exact quadratic phase. -/
lemma quasi_add_nat_tau {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z)
    (m : ℕ) (z : ℂ) : H (z + (m : ℂ) * (τ : ℂ)) =
      (-1 : ℂ) ^ m * Complex.exp (-κ * (m : ℂ) ^ 2 * (τ : ℂ) -
        2 * κ * (m : ℂ) * z) * H z := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show z + ((m + 1 : ℕ) : ℂ) * (τ : ℂ) =
      (z + (m : ℂ) * (τ : ℂ)) + (τ : ℂ) by push_cast; ring, hτ, ih]
    have he : (-κ * (τ : ℂ) - 2 * κ * (z + (m : ℂ) * (τ : ℂ))) +
        (-κ * (m : ℂ) ^ 2 * (τ : ℂ) - 2 * κ * (m : ℂ) * z) =
        -κ * ((m + 1 : ℕ) : ℂ) ^ 2 * (τ : ℂ) -
          2 * κ * ((m + 1 : ℕ) : ℂ) * z := by
      push_cast
      ring
    calc
      _ = (-1 : ℂ) ^ (m + 1) *
          (Complex.exp (-κ * (τ : ℂ) - 2 * κ * (z + (m : ℂ) * (τ : ℂ))) *
            Complex.exp (-κ * (m : ℂ) ^ 2 * (τ : ℂ) - 2 * κ * (m : ℂ) * z)) * H z := by
        rw [pow_succ]
        ring
      _ = _ := by rw [← Complex.exp_add, he]

lemma numerator_add_one {n : ℕ} {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (h1 : ∀ z, H (z + 1) = -H z) (z : ℂ) :
    numerator n τ H (z + 1) = (-1 : ℂ) ^ n * numerator n τ H z := by
  have ha (a : ℂ) : H ((z + 1) + a) = (-1 : ℂ) * H (z + a) := by
    rw [show (z + 1) + a = (z + a) + 1 by ring, h1]
    ring
  calc
    _ = (∏ r : Fin n, ∏ s : Fin n, (-1 : ℂ)) * numerator n τ H z := by
      unfold numerator
      simp_rw [ha]
      simp only [Finset.prod_mul_distrib]
    _ = _ := by
      simp only [Fin.prod_const, ← pow_mul]
      rw [sign_square]

lemma denominator_add_one {n : ℕ} {H : ℂ → ℂ}
    (h1 : ∀ z, H (z + 1) = -H z) (z : ℂ) :
    denominator n H (z + 1) = (-1 : ℂ) ^ n * denominator n H z := by
  have hH : H ((n : ℂ) * (z + 1)) = (-1 : ℂ) ^ n * H ((n : ℂ) * z) := by
    rw [show (n : ℂ) * (z + 1) = (n : ℂ) * z + (n : ℂ) by ring]
    exact quasi_add_nat_one h1 n ((n : ℂ) * z)
  unfold denominator
  rw [hH, show -κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * (z + 1) =
    (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * z) +
      (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ)) by ring,
    Complex.exp_add, exp_degree_phase, mul_one]
  ring

/-- The τ multiplier shared by numerator and compensated denominator. -/
def tauMultiplier (n : ℕ) (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * Complex.exp (-κ * (n : ℂ) * (2 * (n : ℂ) - 1) * (τ : ℂ) -
    2 * κ * (n : ℂ) ^ 2 * z)

/-- Summation of every actual quasi-period exponent, including the
constant even-integer phase. -/
lemma sum_quasi_exponents {n : ℕ} (hn : 0 < n) (τ : UpperHalfPlane) (z : ℂ) :
    (∑ r : Fin n, ∑ s : Fin n, (-κ * (τ : ℂ) - 2 * κ * (z + shift n τ r s))) =
      (-κ * (n : ℂ) * (2 * (n : ℂ) - 1) * (τ : ℂ) - 2 * κ * (n : ℂ) ^ 2 * z) +
        (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ)) := by
  have hterm (r s : Fin n) : -κ * (τ : ℂ) - 2 * κ * (z + shift n τ r s) =
      (-κ * (τ : ℂ) - 2 * κ * z) + (-2 * κ) * shift n τ r s := by ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  rw [sum_shifts hn τ, cast_pred hn]
  ring

lemma numerator_add_tau {n : ℕ} {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hn : 0 < n)
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z) (z : ℂ) :
    numerator n τ H (z + (τ : ℂ)) = tauMultiplier n τ z * numerator n τ H z := by
  have ha (a : ℂ) : H ((z + (τ : ℂ)) + a) =
      (-1 : ℂ) * Complex.exp (-κ * (τ : ℂ) - 2 * κ * (z + a)) * H (z + a) := by
    rw [show (z + (τ : ℂ)) + a = (z + a) + (τ : ℂ) by ring, hτ]
    ring
  calc
    _ = (∏ r : Fin n, ∏ s : Fin n, (-1 : ℂ)) *
        (∏ r : Fin n, ∏ s : Fin n,
          Complex.exp (-κ * (τ : ℂ) - 2 * κ * (z + shift n τ r s))) *
        numerator n τ H z := by
      unfold numerator
      simp_rw [ha]
      simp only [Finset.prod_mul_distrib]
    _ = (-1 : ℂ) ^ n *
        (∏ r : Fin n, ∏ s : Fin n,
          Complex.exp (-κ * (τ : ℂ) - 2 * κ * (z + shift n τ r s))) *
        numerator n τ H z := by
      simp only [Fin.prod_const, ← pow_mul]
      rw [sign_square]
    _ = (-1 : ℂ) ^ n *
        Complex.exp (∑ r : Fin n, ∑ s : Fin n,
          (-κ * (τ : ℂ) - 2 * κ * (z + shift n τ r s))) * numerator n τ H z := by
      simp_rw [← Complex.exp_sum]
    _ = _ := by
      rw [sum_quasi_exponents hn τ z, Complex.exp_add, exp_degree_phase, mul_one]
      rfl

lemma denominator_add_tau {n : ℕ} {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hn : 0 < n)
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z) (z : ℂ) :
    denominator n H (z + (τ : ℂ)) = tauMultiplier n τ z * denominator n H z := by
  have hH : H ((n : ℂ) * (z + (τ : ℂ))) = (-1 : ℂ) ^ n *
      Complex.exp (-κ * (n : ℂ) ^ 2 * (τ : ℂ) - 2 * κ * (n : ℂ) * ((n : ℂ) * z)) *
        H ((n : ℂ) * z) := by
    rw [show (n : ℂ) * (z + (τ : ℂ)) = (n : ℂ) * z + (n : ℂ) * (τ : ℂ) by ring]
    exact quasi_add_nat_tau hτ n ((n : ℂ) * z)
  have he : (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * (z + (τ : ℂ))) +
      (-κ * (n : ℂ) ^ 2 * (τ : ℂ) - 2 * κ * (n : ℂ) * ((n : ℂ) * z)) =
      (-κ * (n : ℂ) * (2 * (n : ℂ) - 1) * (τ : ℂ) - 2 * κ * (n : ℂ) ^ 2 * z) +
        (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * z) := by
    rw [cast_pred hn]
    ring
  unfold denominator
  rw [hH]
  calc
    _ = (-1 : ℂ) ^ n *
        (Complex.exp (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * (z + (τ : ℂ))) *
          Complex.exp (-κ * (n : ℂ) ^ 2 * (τ : ℂ) -
            2 * κ * (n : ℂ) * ((n : ℂ) * z))) * H ((n : ℂ) * z) := by ring
    _ = _ := by
      rw [← Complex.exp_add, he, Complex.exp_add]
      unfold tauMultiplier
      ring

lemma tauMultiplier_ne_zero (n : ℕ) (τ : UpperHalfPlane) (z : ℂ) :
    tauMultiplier n τ z ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Complex.exp_ne_zero _)

/-- The entire regularized quotient of the actual product and scaled
function has both lattice periods. -/
theorem quotient_entire_periodic {n : ℕ} {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hn : 0 < n) (hH : Differentiable ℂ H)
    (h1 : ∀ z, H (z + 1) = -H z)
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z)
    (hzeros : ∀ z, H z = 0 ↔ ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * (τ : ℂ))
    (hd0 : deriv H 0 ≠ 0) :
    Differentiable ℂ (QuasiThetaMultiplicationTwo.regularizedQuotient
      (numerator n τ H) (denominator n H)) ∧
    Function.Periodic (QuasiThetaMultiplicationTwo.regularizedQuotient
      (numerator n τ H) (denominator n H)) 1 ∧
    Function.Periodic (QuasiThetaMultiplicationTwo.regularizedQuotient
      (numerator n τ H) (denominator n H)) (τ : ℂ) := by
  have hP := differentiable_numerator (n := n) (τ := τ) hH
  have hE := differentiable_denominator (n := n) hH
  have hdivisor : ∀ c, denominator n H c = 0 →
      numerator n τ H c = 0 ∧ deriv (denominator n H) c ≠ 0 := by
    intro c hc
    exact ⟨(numerator_zero_iff_denominator_zero hn hzeros c).mpr hc,
      denominator_deriv_ne_zero_at_zero hn hH h1 hτ hzeros hd0 hc⟩
  refine ⟨QuasiThetaMultiplicationTwo.differentiable_regularizedQuotient hP hE hdivisor, ?_, ?_⟩
  · exact QuasiThetaMultiplicationTwo.periodic_regularizedQuotient
      (A := fun _ => (-1 : ℂ) ^ n) hP hE hdivisor (fun _ => pow_ne_zero _ (by norm_num))
      (numerator_add_one h1) (denominator_add_one h1)
  · exact QuasiThetaMultiplicationTwo.periodic_regularizedQuotient
      (A := tauMultiplier n τ) hP hE hdivisor (tauMultiplier_ne_zero n τ)
      (numerator_add_tau hn hτ) (denominator_add_tau hn hτ)

/-- The test point is scaled to the nonlattice point `1/2`. -/
lemma denominator_test_ne_zero {n : ℕ} {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hn : 0 < n)
    (hzeros : ∀ z, H z = 0 ↔ ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * (τ : ℂ)) :
    denominator n H (1 / (2 * (n : ℂ))) ≠ 0 := by
  have hscale : (n : ℂ) * (1 / (2 * (n : ℂ))) = 1 / 2 := by
    field_simp [cast_ne_zero hn]
  intro hz
  have hh := (denominator_zero_iff (n := n) (H := H) (1 / (2 * (n : ℂ)))).mp hz
  rw [hscale] at hh
  exact QuasiThetaMultiplicationTwo.half_ne_zero hzeros hh

/-- Multiplication for every positive natural degree, with an actual
nonzero constant and equality at every point, including the zero divisor. -/
theorem multiplication_nat {n : ℕ} {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hn : 0 < n) (hH : Differentiable ℂ H)
    (h1 : ∀ z, H (z + 1) = -H z)
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z)
    (hzeros : ∀ z, H z = 0 ↔ ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * (τ : ℂ))
    (hd0 : deriv H 0 ≠ 0) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ,
      (∏ r : Fin n, ∏ s : Fin n, H (z + ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (n : ℂ))) =
        C * Complex.exp (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * z) * H ((n : ℂ) * z) := by
  obtain ⟨hQ, hQ1, hQτ⟩ := quotient_entire_periodic hn hH h1 hτ hzeros hd0
  have hb := QuasiThetaMultiplicationTwo.bounded_of_continuous_periodic hQ.continuous hQ1 hQτ
  let w : ℂ := 1 / (2 * (n : ℂ))
  let C : ℂ := QuasiThetaMultiplicationTwo.regularizedQuotient (numerator n τ H) (denominator n H) w
  have hc (z : ℂ) : QuasiThetaMultiplicationTwo.regularizedQuotient
      (numerator n τ H) (denominator n H) z = C :=
    hQ.apply_eq_apply_of_bounded hb z w
  have hEw : denominator n H w ≠ 0 := denominator_test_ne_zero hn hzeros
  have hPw : numerator n τ H w ≠ 0 := by
    intro hp
    exact hEw ((numerator_zero_iff_denominator_zero hn hzeros w).mp hp)
  have hC : C ≠ 0 := by
    dsimp [C, QuasiThetaMultiplicationTwo.regularizedQuotient]
    rw [ite_eq_right hEw]
    exact div_ne_zero hPw hEw
  refine ⟨C, hC, ?_⟩
  intro z
  have hidentity := QuasiThetaMultiplicationTwo.regularizedQuotient_mul
    (fun u hu => (numerator_zero_iff_denominator_zero hn hzeros u).mpr hu) z
  rw [hc z] at hidentity
  change numerator n τ H z =
    C * Complex.exp (-κ * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * z) * H ((n : ℂ) * z)
  simpa only [denominator, mul_assoc] using hidentity.symm

/-- Literal generic interface with the five independent analytic premises
and a strictly positive degree. -/
theorem multiplication_nat_explicit (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) (H : ℂ → ℂ)
    (hEntire : Differentiable ℂ H)
    (hOne : ∀ z : ℂ, H (z + 1) = -H z)
    (hTau : ∀ z : ℂ, H (z + (τ : ℂ)) =
      -Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ : ℂ) -
        2 * (Real.pi : ℂ) * Complex.I * z) * H z)
    (hZeroSet : ∀ z : ℂ, H z = 0 ↔
      ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * (τ : ℂ))
    (hDerivative : deriv H 0 ≠ 0) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ,
      (∏ r : Fin n, ∏ s : Fin n,
        H (z + ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (n : ℂ))) =
        C * Complex.exp (-(Real.pi : ℂ) * Complex.I * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * z) *
          H ((n : ℂ) * z) := by
  have hTau' : ∀ z : ℂ, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z := by
    intro z
    simpa only [mul_assoc, neg_mul] using hTau z
  obtain ⟨C, hC, hformula⟩ := multiplication_nat hn hEntire hOne hTau' hZeroSet hDerivative
  refine ⟨C, hC, ?_⟩
  intro z
  simpa only [mul_assoc, neg_mul] using hformula z

end QuasiThetaMultiplicationNat
