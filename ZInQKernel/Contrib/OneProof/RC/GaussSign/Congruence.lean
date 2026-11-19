import Mathlib.NumberTheory.Wilson
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.Nat.Factorial.BigOperators

/-! The cyclotomic sign comparison, on-the-spot (c), for tex 8731–8753
and 9000–9004. After translating by one, the two polynomials have the
same nonzero coefficient in degree `(p - 1) / 2` modulo `p`. -/

noncomputable section

namespace ZInQ.Manuscript.RC.GaussSign

open Polynomial
open scoped BigOperators Nat

/-- The polynomial whose evaluation at the chosen root sums the phases
over all squares, with multiplicities. -/
def squarePolynomial (p : ℕ) [NeZero p] (R : Type*) [CommRing R] : R[X] :=
  ∑ x : ZMod p, X ^ (x ^ 2).val

/-- The product over the odd representatives of the pairs of opposite
nonzero residues, with (p=2m+1). -/
def oddProductPolynomial (p m : ℕ) (R : Type*) [CommRing R] : R[X] :=
  ∏ j ∈ Finset.range m, (X ^ (2 * j + 1) - X ^ (p - (2 * j + 1)))

private theorem sum_eval_monic (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X])
    (hf : f.Monic) (hd : f.natDegree = p - 1) :
    ∑ x : ZMod p, f.eval x = -1 := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hlead : f.coeff (p - 1) = 1 := hd ▸ hf.coeff_natDegree
  have heval (x : ZMod p) :
      f.eval x = ∑ j ∈ Finset.range (p - 1 + 1), f.coeff j * x ^ j := by
    conv_lhs => rw [f.as_sum_range_C_mul_X_pow]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, hd]
  simp_rw [heval]
  rw [Finset.sum_comm, Finset.sum_range_succ]
  simp_rw [← Finset.mul_sum]
  have hzero : (∑ j ∈ Finset.range (p - 1), f.coeff j * ∑ x : ZMod p, x ^ j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [FiniteField.sum_pow_lt_card_sub_one (ZMod p) j
      (by simpa only [ZMod.card] using Finset.mem_range.mp hj), mul_zero]
  rw [hzero, hlead, one_mul, zero_add]
  have he (x : ZMod p) : x ^ (p - 1) = if x = 0 then 0 else 1 := by
    split_ifs with h
    · simp [h, show p - 1 ≠ 0 by omega]
    · exact ZMod.pow_card_sub_one_eq_one h
  have he' (x : ZMod p) : x ^ (p - 1) = 1 - (if x = 0 then 1 else 0) := by
    rw [he]
    split_ifs <;> simp
  simp_rw [he', Finset.sum_sub_distrib]
  simp [ZMod.card]

private theorem factorial_mul_choose_eq (p m : ℕ) [Fact p.Prime] (x : ZMod p) :
    (m ! : ZMod p) * ((x ^ 2).val.choose m : ZMod p) =
      ∏ j ∈ Finset.range m, (x ^ 2 - (j : ZMod p)) := by
  rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
    Nat.cast_prod]
  by_cases h : m ≤ (x ^ 2).val
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Nat.cast_sub (by have := Finset.mem_range.mp hj; omega), ZMod.natCast_zmod_val]
  · have hj : (x ^ 2).val ∈ Finset.range m := Finset.mem_range.mpr (by omega)
    rw [Finset.prod_eq_zero hj, Finset.prod_eq_zero hj]
    · simp
    · simp

private theorem square_coeff (p m : ℕ) [Fact p.Prime] (hm : 2 * m = p - 1) :
    (m ! : ZMod p) * ((squarePolynomial p (ZMod p)).comp (X + 1)).coeff m = -1 := by
  classical
  simp only [squarePolynomial, sum_comp, X_pow_comp, finsetSum_coeff,
    coeff_X_add_one_pow, Finset.mul_sum, factorial_mul_choose_eq]
  let f : (ZMod p)[X] := ∏ j ∈ Finset.range m, (X ^ (2 : ℕ) - C (j : ZMod p))
  have hmon : ∀ j ∈ Finset.range m, (X ^ (2 : ℕ) - C (j : ZMod p)).Monic :=
    fun j _ => monic_X_pow_sub_C _ (by decide)
  have hf : f.Monic := monic_prod_of_monic _ _ hmon
  have hd : f.natDegree = p - 1 := by
    dsimp [f]
    rw [natDegree_prod_of_monic _ _ hmon]
    simp only [natDegree_X_pow_sub_C]
    simp [← hm, Nat.mul_comm]
  simpa only [f, eval_prod, eval_sub, eval_pow, eval_X, eval_C] using sum_eval_monic p f hf hd

private theorem coeff_product_of_X_dvd {R : Type*} [CommRing R] (f : ℕ → R[X])
    (n : ℕ) (hf : ∀ j ∈ Finset.range n, X ∣ f j) :
    (∏ j ∈ Finset.range n, f j).coeff n = ∏ j ∈ Finset.range n, (f j).coeff 1 := by
  classical
  have he (j : ℕ) : ∃ q : R[X], j ∈ Finset.range n → f j = X * q := by
    by_cases hj : j ∈ Finset.range n
    · obtain ⟨q, hq⟩ := hf j hj
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose q hq using he
  calc
    _ = (∏ j ∈ Finset.range n, X * q j).coeff n := by
      exact congrArg (fun q : R[X] => q.coeff n) (Finset.prod_congr rfl hq)
    _ = (∏ j ∈ Finset.range n, q j).coeff 0 := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      simpa using coeff_X_pow_mul (∏ j ∈ Finset.range n, q j) n 0
    _ = _ := by
      rw [coeff_zero_eq_eval_zero, eval_prod]
      apply Finset.prod_congr rfl
      intro j hj
      rw [hq j hj, ← coeff_zero_eq_eval_zero]
      exact (coeff_X_mul _ 0).symm

private theorem twice_odd_factorial (n : ℕ) :
    n ! * (∏ j ∈ Finset.range n, 2 * (2 * j + 1)) = (2 * n)! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Nat.factorial_succ, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ, ← ih]
    ring

private theorem product_coeff (p m : ℕ) [Fact p.Prime] (hm : 2 * m + 1 = p) :
    (m ! : ZMod p) * ((oddProductPolynomial p m (ZMod p)).comp (X + 1)).coeff m = -1 := by
  simp only [oddProductPolynomial, prod_comp, sub_comp, pow_comp, X_comp]
  rw [coeff_product_of_X_dvd]
  · have he (j : ℕ) (hj : j ∈ Finset.range m) :
        (((X + 1) ^ (2 * j + 1) - (X + 1) ^ (p - (2 * j + 1)) : (ZMod p)[X]).coeff 1)
          = ((2 * (2 * j + 1) : ℕ) : ZMod p) := by
      have hj' : 2 * j + 1 ≤ p := by have := Finset.mem_range.mp hj; omega
      simp only [coeff_sub, coeff_X_add_one_pow, Nat.choose_one_right, Nat.cast_sub hj',
        ZMod.natCast_self, zero_sub]
      push_cast
      ring
    rw [Finset.prod_congr rfl he, ← Nat.cast_prod, ← Nat.cast_mul, twice_odd_factorial,
      show 2 * m = p - 1 by omega, ZMod.wilsons_lemma]
  · intro j _
    rw [X_dvd_iff, coeff_sub, coeff_X_add_one_pow, coeff_X_add_one_pow]
    simp

private theorem shifted_cyclotomic (p : ℕ) [Fact p.Prime] :
    (cyclotomic p (ZMod p)).comp (X + 1) = X ^ (p - 1) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have he := congrArg (fun f : (ZMod p)[X] => f.comp (X + 1))
    (cyclotomic_prime_mul_X_sub_one (ZMod p) p)
  simp only [mul_comp, pow_comp, sub_comp, one_comp, X_comp, add_sub_cancel_right] at he
  rw [add_pow_char, one_pow, add_sub_cancel_right] at he
  apply mul_right_cancel₀ (X_ne_zero (R := ZMod p))
  rwa [← pow_succ, Nat.sub_add_cancel hp]

private theorem shifted_coeff_eq_zero (p m : ℕ) [Fact p.Prime] (hm : m < p - 1)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (f : ℤ[X]) (hf : aeval ζ f = 0) :
    ((f.map (Int.castRingHom (ZMod p))).comp (X + 1)).coeff m = 0 := by
  obtain ⟨g, hg⟩ : cyclotomic p ℤ ∣ f := by
    rw [cyclotomic_eq_minpoly hζ (Fact.out : p.Prime).pos]
    exact minpoly.isIntegrallyClosed_dvd (hζ.isIntegral (Fact.out : p.Prime).pos) hf
  rw [hg, Polynomial.map_mul, map_cyclotomic, mul_comp, shifted_cyclotomic,
    coeff_X_pow_mul', ite_eq_right (by omega)]

/-- If the evaluations agree up to sign, their shared translated
coefficient excludes the negative sign. -/
theorem eval_squarePolynomial_eq_of_sq (p m : ℕ) [Fact p.Prime] (hm : 2 * m + 1 = p)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p)
    (hs : (aeval ζ (squarePolynomial p ℤ)) ^ 2 =
      (aeval ζ (oddProductPolynomial p m ℤ)) ^ 2) :
    aeval ζ (squarePolynomial p ℤ) = aeval ζ (oddProductPolynomial p m ℤ) := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · exact h
  · exfalso
    let f := squarePolynomial p ℤ + oddProductPolynomial p m ℤ
    have hf : aeval ζ f = 0 := by simp [f, h]
    have hz := shifted_coeff_eq_zero p m (by omega) ζ hζ f hf
    simp only [f, Polynomial.map_add, squarePolynomial, oddProductPolynomial,
      Polynomial.map_sum, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_pow,
      map_X, add_comp, coeff_add] at hz
    change ((squarePolynomial p (ZMod p)).comp (X + 1)).coeff m +
      ((oddProductPolynomial p m (ZMod p)).comp (X + 1)).coeff m = 0 at hz
    have he := congrArg (fun x : ZMod p => (m ! : ZMod p) * x) hz
    simp only [mul_add, mul_zero, square_coeff p m (by omega), product_coeff p m hm] at he
    have hn : (2 : ZMod p) ≠ 0 := by
      change ((2 : ℕ) : ZMod p) ≠ 0
      exact fun h0 => (show 2 < p by omega).not_ge
        (Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 2 p).mp h0))
    exact hn (by linear_combination -he)

#print axioms sum_eval_monic
#print axioms factorial_mul_choose_eq
#print axioms square_coeff
#print axioms coeff_product_of_X_dvd
#print axioms twice_odd_factorial
#print axioms product_coeff
#print axioms shifted_cyclotomic
#print axioms shifted_coeff_eq_zero
#print axioms eval_squarePolynomial_eq_of_sq

end ZInQ.Manuscript.RC.GaussSign
