import ZInQKernel.Contrib.OneProof.RC.GaussSign.Congruence
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The square and phase of the product of root differences,
on-the-spot (c), for tex 8731–8753 and 9000–9004. -/

noncomputable section

namespace ZInQ.Manuscript.RC.GaussSign

open Polynomial
open scoped BigOperators Real

private theorem prod_odd_complement {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    (∏ j ∈ Finset.range m, (f (2 * j + 1) * f (2 * m + 1 - (2 * j + 1)))) =
      ∏ j ∈ Finset.range (2 * m), f (j + 1) := by
  rw [Finset.prod_mul_distrib]
  have he : (∏ j ∈ Finset.range m, f (2 * m + 1 - (2 * j + 1))) =
      ∏ j ∈ Finset.range m, f (2 * j + 2) := by
    rw [← Finset.prod_range_reflect (fun j => f (2 * j + 2)) m]
    apply Finset.prod_congr rfl
    intro j hj
    congr 1
    have := Finset.mem_range.mp hj
    omega
  rw [he, ← Finset.prod_mul_distrib]
  clear he
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
      Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc]

/-- Squaring the half product recovers the full cyclotomic product,
with one minus sign per pair of opposite residues. -/
theorem eval_oddProduct_sq (p m : ℕ) [Fact p.Prime] (hm : 2 * m + 1 = p)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) :
    (aeval ζ (oddProductPolynomial p m ℤ)) ^ 2 = (-1 : ℂ) ^ m * p := by
  have hp : 2 < p := by have := (Fact.out : p.Prime).one_lt; omega
  have hζ₂ : IsPrimitiveRoot (ζ ^ 2) p :=
    hζ.pow_of_coprime 2 ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (fun hd => (not_le_of_gt hp) (Nat.le_of_dvd (by decide) hd))).symm
  have hfull : (∏ j ∈ Finset.range (2 * m), (1 - (ζ ^ 2) ^ (j + 1))) = (p : ℂ) := by
    rw [← hm] at hζ₂ ⊢
    simpa only [Nat.cast_add, Nat.cast_one] using hζ₂.prod_one_sub_pow_eq_order
  have hfactor (j : ℕ) (hj : j ∈ Finset.range m) :
      (ζ ^ (2 * j + 1) - ζ ^ (p - (2 * j + 1))) ^ 2 =
        -1 * ((1 - (ζ ^ 2) ^ (2 * j + 1)) * (1 - (ζ ^ 2) ^ (p - (2 * j + 1)))) := by
    have hj' := Finset.mem_range.mp hj
    let x := ζ ^ (2 * j + 1)
    let y := ζ ^ (p - (2 * j + 1))
    have hxy : x * y = 1 := by
      dsimp [x, y]
      rw [← pow_add, show 2 * j + 1 + (p - (2 * j + 1)) = p by omega, hζ.pow_eq_one]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 (2 * j + 1), Nat.mul_comm 2 (p - (2 * j + 1)),
      pow_mul, pow_mul]
    change (x - y) ^ 2 = -1 * ((1 - x ^ 2) * (1 - y ^ 2))
    calc
      _ = x ^ 2 + y ^ 2 - 2 * (x * y) := by ring
      _ = x ^ 2 + y ^ 2 - 1 - (x * y) ^ 2 := by rw [hxy]; ring
      _ = _ := by ring
  simp only [oddProductPolynomial, map_prod, map_sub, map_pow, aeval_X]
  have hpaired := prod_odd_complement (fun a => 1 - (ζ ^ 2) ^ a) m
  rw [hm] at hpaired
  rw [← Finset.prod_pow, Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_range, hpaired, hfull]

/-- The primitive root for the negative finite additive character. -/
def negativeRoot (p : ℕ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / p))

theorem negativeRoot_primitive (p : ℕ) (hp : p ≠ 0) :
    IsPrimitiveRoot (negativeRoot p) p := by
  rw [negativeRoot, Complex.exp_neg]
  exact (Complex.isPrimitiveRoot_exp p hp).inv

private theorem root_difference_sine (p a : ℕ) (hp : 0 < p) (ha : a ≤ p) :
    negativeRoot p ^ a - negativeRoot p ^ (p - a) =
      -Complex.I * ((2 * Real.sin (2 * Real.pi * a / p) : ℝ) : ℂ) := by
  let t : ℝ := 2 * Real.pi * a / p
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have he₁ : negativeRoot p ^ a = Complex.exp ((-(t : ℂ)) * Complex.I) := by
    rw [negativeRoot, ← Complex.exp_nat_mul]
    push_cast [t]
    ring
  have he₂ : negativeRoot p ^ (p - a) = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [negativeRoot, ← Complex.exp_nat_mul, Nat.cast_sub ha]
    have h :
        ((p : ℂ) - a) * -(2 * (Real.pi : ℂ) * Complex.I / p) =
          (t : ℂ) * Complex.I + -(2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast [t]
      field_simp
      ring
    rw [h, Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]
  change negativeRoot p ^ a - negativeRoot p ^ (p - a) = -Complex.I * ((2 * Real.sin t : ℝ) : ℂ)
  rw [he₁, he₂, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_sin]
  push_cast
  ring

private theorem sine_sign (p m j : ℕ) (hm : 2 * m + 1 = p) (hj : j < m) :
    let s := Real.sin (2 * Real.pi * (2 * j + 1 : ℕ) / p)
    (if j < (m + 1) / 2 then 0 < s else s < 0) := by
  let t : ℝ := 2 * Real.pi * (2 * j + 1 : ℕ) / p
  change if j < (m + 1) / 2 then 0 < Real.sin t else Real.sin t < 0
  have hp' : 0 < (p : ℝ) := Nat.cast_pos.mpr (by omega)
  have ha : 0 < ((2 * j + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hb : ((2 * j + 1 : ℕ) : ℝ) < p := Nat.cast_lt.mpr (by omega)
  have hpos : 0 < t := div_pos (by positivity) hp'
  have hupper : t < 2 * Real.pi := (div_lt_iff₀ hp').mpr (by gcongr)
  split_ifs with h
  · have hl : 2 * ((2 * j + 1 : ℕ) : ℝ) < p := by exact_mod_cast (show 2 * (2 * j + 1) < p by omega)
    apply Real.sin_pos_of_pos_of_lt_pi hpos
    apply (div_lt_iff₀ hp').mpr
    nlinarith [mul_lt_mul_of_pos_right hl Real.pi_pos]
  · have hl : (p : ℝ) < 2 * ((2 * j + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show p < 2 * (2 * j + 1) by omega)
    have hlow : Real.pi < t := by
      apply (lt_div_iff₀ hp').mpr
      nlinarith [mul_lt_mul_of_pos_right hl Real.pi_pos]
    have h := Real.sin_pos_of_pos_of_lt_pi (show 0 < t - Real.pi by linarith)
      (show t - Real.pi < Real.pi by linarith)
    rw [Real.sin_sub_pi] at h
    linarith

private theorem prod_signs (m : ℕ) :
    (∏ j ∈ Finset.range m, (if j < (m + 1) / 2 then (1 : ℂ) else -1)) =
      (-1 : ℂ) ^ (m / 2) := by
  let k := (m + 1) / 2
  change (∏ j ∈ Finset.range m, (if j < k then (1 : ℂ) else -1)) = _
  conv_lhs => rw [show m = k + m / 2 by dsimp [k]; omega, Finset.prod_range_add]
  have h₁ : (∏ j ∈ Finset.range k, (if j < k then (1 : ℂ) else -1)) = 1 :=
    Finset.prod_eq_one fun j hj => ite_eq_left (Finset.mem_range.mp hj)
  have h₂ : (∏ j ∈ Finset.range (m / 2), (if k + j < k then (1 : ℂ) else -1)) =
      (-1 : ℂ) ^ (m / 2) := by
    simp [Nat.not_lt.mpr (Nat.le_add_right k _)]
  rw [h₁, h₂, one_mul]

/-- Its phase is (1) or (-i) for the root with negative argument.
The positive amplitude is fixed by the square. -/
theorem eval_oddProduct_negativeRoot (p m : ℕ) [Fact p.Prime] (hm : 2 * m + 1 = p) :
    aeval (negativeRoot p) (oddProductPolynomial p m ℤ) =
      (-Complex.I) ^ (m % 2) * (Real.sqrt p : ℂ) := by
  let s (j : ℕ) := Real.sin (2 * Real.pi * (2 * j + 1 : ℕ) / p)
  let A : ℝ := ∏ j ∈ Finset.range m, 2 * |s j|
  have hsign (j : ℕ) (hj : j ∈ Finset.range m) :
      (2 * s j : ℝ) = (if j < (m + 1) / 2 then 1 else -1) * (2 * |s j|) := by
    have hh := sine_sign p m j hm (Finset.mem_range.mp hj)
    change (if j < (m + 1) / 2 then 0 < s j else s j < 0) at hh
    split_ifs at hh ⊢
    · simp [abs_of_pos hh]
    · rw [abs_of_neg hh]; ring
  have hA : 0 < A := by
    apply Finset.prod_pos
    intro j hj
    have hh := sine_sign p m j hm (Finset.mem_range.mp hj)
    change (if j < (m + 1) / 2 then 0 < s j else s j < 0) at hh
    split_ifs at hh
    · exact mul_pos (by norm_num) (abs_pos.mpr hh.ne')
    · exact mul_pos (by norm_num) (abs_pos.mpr hh.ne)
  have hI : (-Complex.I) ^ 2 = -1 := by rw [neg_sq, Complex.I_sq]
  have hphase : (-Complex.I) ^ m * (-1 : ℂ) ^ (m / 2) = (-Complex.I) ^ (m % 2) := by
    calc
      _ = (-Complex.I) ^ (m % 2 + 2 * (m / 2)) * (-1 : ℂ) ^ (m / 2) :=
        congrArg (fun n => (-Complex.I) ^ n * (-1 : ℂ) ^ (m / 2)) (by omega)
      _ = _ := by
        rw [pow_add, pow_mul, hI, mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one]
  have he :
      aeval (negativeRoot p) (oddProductPolynomial p m ℤ) =
        (-Complex.I) ^ (m % 2) * (A : ℂ) := by
    simp only [oddProductPolynomial, map_prod, map_sub, map_pow, aeval_X]
    have hfactor (j : ℕ) (hj : j ∈ Finset.range m) :
        negativeRoot p ^ (2 * j + 1) - negativeRoot p ^ (p - (2 * j + 1)) =
          -Complex.I * ((if j < (m + 1) / 2 then (1 : ℂ) else -1) * ((2 * |s j| : ℝ) : ℂ)) := by
      have hj' := Finset.mem_range.mp hj
      rw [root_difference_sine p (2 * j + 1) (by omega) (by omega)]
      change -Complex.I * ((2 * s j : ℝ) : ℂ) = _
      rw [hsign j hj, Complex.ofReal_mul]
      split_ifs <;> push_cast <;> rfl
    rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_mul_distrib, prod_signs, ← Complex.ofReal_prod]
    change (-Complex.I) ^ m * ((-1 : ℂ) ^ (m / 2) * (A : ℂ)) = _
    rw [← mul_assoc, hphase]
  have hsq := eval_oddProduct_sq p m hm _ (negativeRoot_primitive p (by omega))
  rw [he, mul_pow, ← pow_mul, Nat.mul_comm (m % 2) 2, pow_mul, hI] at hsq
  have hh : (-1 : ℂ) ^ m = (-1) ^ (m % 2) := by
    conv_lhs => rw [show m = m % 2 + 2 * (m / 2) by omega]
    rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  rw [hh] at hsq
  have hAsq : A ^ 2 = (p : ℝ) := by
    exact_mod_cast (mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) hsq)
  have hr : A = Real.sqrt p := (Real.sqrt_sq hA.le).symm.trans (congrArg Real.sqrt hAsq)
  rw [he, hr]

#print axioms prod_odd_complement
#print axioms eval_oddProduct_sq
#print axioms negativeRoot_primitive
#print axioms root_difference_sine
#print axioms sine_sign
#print axioms prod_signs
#print axioms eval_oddProduct_negativeRoot

end ZInQ.Manuscript.RC.GaussSign
