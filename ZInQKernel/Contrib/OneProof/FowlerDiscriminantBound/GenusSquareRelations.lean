module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-! Squarefree principal relations in the genus argument for imaginary quadratic fields. -/

public section

namespace HDec.CMBranch.FowlerArithmetic

open NumberField

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

private theorem complex_im_eq_zero_of_sq {z : ℂ} {a : ℝ} (ha : 0 ≤ a)
    (h : z ^ 2 = (a : ℂ)) : z.im = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im] at hre him
  have hprod : z.re * z.im = 0 := by linarith
  rcases mul_eq_zero.mp hprod with h0 | h0
  · rw [h0] at hre
    nlinarith [sq_nonneg z.im]
  · exact h0

/-- If an element in an imaginary quadratic field has nonnegative rational square,
then it is rational. A nonrational element would generate the field and give a real embedding. -/
theorem exists_rat_of_sq_nonneg_rat (hk : Module.finrank ℚ K = 2) {x : K} {q : ℚ}
    (hq : 0 ≤ q) (hx : x ^ 2 = algebraMap ℚ K q) :
    ∃ r : ℚ, algebraMap ℚ K r = x := by
  let := IntermediateField.isSimpleOrder_of_finrank_prime ℚ K (hk.symm ▸ Nat.prime_two)
  have hmem := IntermediateField.mem_adjoin_simple_self ℚ x
  rcases IsSimpleOrder.eq_bot_or_eq_top (IntermediateField.adjoin ℚ {x}) with hbot | htop
  · rw [hbot, IntermediateField.mem_bot] at hmem
    exact hmem
  · let e : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom
    have hsq : e x ^ 2 = ((q : ℝ) : ℂ) := by
      have he := congrArg e hx
      change e (x ^ 2) = e (q : K) at he
      simpa only [map_pow, map_ratCast, Complex.ofReal_ratCast] using he
    have hconj : ComplexEmbedding.conjugate e x = e x :=
      Complex.conj_eq_iff_im.mpr (complex_im_eq_zero_of_sq (by exact_mod_cast hq) hsq)
    apply False.elim (IsTotallyComplex.complexEmbedding_not_isReal e (?_ : _))
    apply ComplexEmbedding.isReal_iff.mpr
    ext y
    have hy : y ∈ IntermediateField.adjoin ℚ {x} := by rw [htop]; exact trivial
    exact IntermediateField.adjoin_induction ℚ
      (motive := fun z _ => ComplexEmbedding.conjugate e z = e z)
      (fun z hz => (Set.mem_singleton_iff.mp hz).symm ▸ hconj)
      (fun r => by change ComplexEmbedding.conjugate e (r : K) = e (r : K); simp)
      (fun z w _ _ hz hw => by rw [map_add, map_add, hz, hw])
      (fun z _ hz => by rw [map_inv₀, map_inv₀, hz])
      (fun z w _ _ hz hw => by rw [map_mul, map_mul, hz, hw]) hy

/-- A positive squarefree rational integer that is a square in an imaginary quadratic
field is 1. -/
theorem squarefree_nat_eq_one_of_sq (hk : Module.finrank ℚ K = 2)
    {m : ℕ} (hm : Squarefree m) {x : K} (hx : x ^ 2 = (m : K)) : m = 1 := by
  obtain ⟨r, hr⟩ := exists_rat_of_sq_nonneg_rat hk (q := (m : ℚ)) (by positivity)
    (by simpa using hx)
  have hsq : r ^ 2 = (m : ℚ) := (algebraMap ℚ K).injective (by simpa [map_pow, hr] using hx)
  have hsqN : IsSquare m := Rat.isSquare_natCast_iff.mp ⟨r, by simpa [pow_two] using hsq.symm⟩
  exact Nat.dvd_one.mp (hm.dvd_of_isSquare_mul (by simpa only [mul_one] using hsqN))

/-- At most one positive squarefree integer has its negative a square in a fixed imaginary
quadratic field. Compare the two roots after multiplying them in that same field. -/
theorem squarefree_nat_eq_of_neg_sq (hk : Module.finrank ℚ K = 2)
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) {x y : K}
    (hx : x ^ 2 = -(m : K)) (hy : y ^ 2 = -(n : K)) : m = n := by
  have hxy : (x * y) ^ 2 = ((m * n : ℕ) : K) := by rw [mul_pow, hx, hy, neg_mul_neg, Nat.cast_mul]
  obtain ⟨r, hr⟩ := exists_rat_of_sq_nonneg_rat hk (q := ((m * n : ℕ) : ℚ)) (by positivity)
    (by simpa using hxy)
  have hsq : r ^ 2 = ((m * n : ℕ) : ℚ) :=
    (algebraMap ℚ K).injective (by simpa [map_pow, hr] using hxy)
  have hs : IsSquare (m * n) := Rat.isSquare_natCast_iff.mp ⟨r, by simpa [pow_two] using hsq.symm⟩
  exact Nat.dvd_antisymm (hm.dvd_of_isSquare_mul hs)
    (hn.dvd_of_isSquare_mul (mul_comm m n ▸ hs))

/-- An injective squarefree product reading on principal relations has at most two values:
`1` and the unique possible nontrivial squarefree negative radicand of the field. -/
theorem card_le_two_of_squarefree_square_relations (hk : Module.finrank ℚ K = 2)
    {A : Type*} (m : A → ℕ) (hm : Function.Injective m) (hs : ∀ a, Squarefree (m a))
    (h : ∀ a, ∃ x : K, x ^ 2 = (m a : K) ∨ x ^ 2 = -(m a : K)) : Nat.card A ≤ 2 := by
  classical
  let f : A → Bool := fun a => decide (m a = 1)
  have hf : Function.Injective f := by
    intro a b hab
    by_cases ha : m a = 1
    · have hb : m b = 1 := by simpa [f, ha] using hab.symm
      exact hm (ha.trans hb.symm)
    · have hb : m b ≠ 1 := by simpa [f, ha] using hab.symm
      obtain ⟨x, hx | hx⟩ := h a
      · exact (ha (squarefree_nat_eq_one_of_sq hk (hs a) hx)).elim
      obtain ⟨y, hy | hy⟩ := h b
      · exact (hb (squarefree_nat_eq_one_of_sq hk (hs b) hy)).elim
      exact hm (squarefree_nat_eq_of_neg_sq hk (hs a) (hs b) hx hy)
  simpa using Nat.card_le_card_of_injective f hf

end HDec.CMBranch.FowlerArithmetic
