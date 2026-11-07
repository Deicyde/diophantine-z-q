import ZInQKernel.Size.Norms.Estimates

/-!
# The weighted pair norm

Blueprint: `size/norms/pair-norm.md`.

The weighted norm `‖a + b s‖ = ‖a‖₁ + 2‖b‖₁` on `S[s] = S[t]/(t² - 2)` is subadditive,
submultiplicative and homogeneous for integer scalars; the degree `max (deg a) (deg b)` is
subadditive under products and bounded by the maximum under sums.
-/

namespace ZInQ.Size

open MvPolynomial
open ZInQ.Syntax (l1 l1_C l1_X l1_neg l1_add_le l1_sub_le l1_mul_le l1_zero l1_one)

variable {σ : Type*}

/-! ### Norms -/

theorem pairNorm_add_le (u v : PairRing σ) : pairNorm (u + v) ≤ pairNorm u + pairNorm v := by
  have h1 := l1_add_le u.re v.re
  have h2 := l1_add_le u.im v.im
  simp only [pairNorm, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
  omega

theorem pairNorm_neg (u : PairRing σ) : pairNorm (-u) = pairNorm u := by
  simp only [pairNorm, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, l1_neg]

theorem pairNorm_sub_le (u v : PairRing σ) : pairNorm (u - v) ≤ pairNorm u + pairNorm v := by
  have h1 := l1_sub_le u.re v.re
  have h2 := l1_sub_le u.im v.im
  simp only [pairNorm, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub]
  omega

theorem pairNorm_smul (c : ℤ) (u : PairRing σ) : pairNorm (c • u) = c.natAbs * pairNorm u := by
  simp only [pairNorm, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, l1_smul]
  ring

theorem pairNorm_intCast_mul (c : ℤ) (u : PairRing σ) :
    pairNorm ((c : PairRing σ) * u) = c.natAbs * pairNorm u := by
  rw [← zsmul_eq_mul, pairNorm_smul]

theorem pairNorm_mul_le (u v : PairRing σ) : pairNorm (u * v) ≤ pairNorm u * pairNorm v := by
  have hre : l1 (u * v).re ≤ l1 u.re * l1 v.re + 2 * (l1 u.im * l1 v.im) := by
    rw [QuadraticAlgebra.re_mul]
    refine (l1_add_le _ _).trans (Nat.add_le_add (l1_mul_le _ _) ?_)
    refine (l1_mul_le _ _).trans ?_
    refine (Nat.mul_le_mul_right _ (l1_mul_le _ _)).trans (le_of_eq ?_)
    rw [l1_ofNat]; ring
  have him : l1 (u * v).im ≤ l1 u.re * l1 v.im + l1 u.im * l1 v.re := by
    rw [QuadraticAlgebra.im_mul, zero_mul, zero_mul, add_zero]
    exact (l1_add_le _ _).trans (Nat.add_le_add (l1_mul_le _ _) (l1_mul_le _ _))
  simp only [pairNorm]
  nlinarith [hre, him, Nat.zero_le (l1 u.re * l1 v.im), Nat.zero_le (l1 u.im * l1 v.re),
    Nat.zero_le (l1 u.im * l1 v.im)]

theorem pairNorm_one : pairNorm (1 : PairRing σ) = 1 := by
  simp [pairNorm, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, l1_one]

theorem pairNorm_pow_le (u : PairRing σ) (k : ℕ) : pairNorm (u ^ k) ≤ pairNorm u ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, pairNorm_one]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (pairNorm_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

/-- Each component is bounded by the pair norm. -/
theorem l1_re_le_pairNorm (u : PairRing σ) : l1 u.re ≤ pairNorm u := by
  rw [pairNorm]; omega

theorem l1_im_le_pairNorm (u : PairRing σ) : l1 u.im ≤ pairNorm u := by
  rw [pairNorm]; omega

/-! ### Degrees -/

theorem totalDegree_re_le_pairDeg (u : PairRing σ) : u.re.totalDegree ≤ pairDeg u :=
  le_max_left _ _

theorem totalDegree_im_le_pairDeg (u : PairRing σ) : u.im.totalDegree ≤ pairDeg u :=
  le_max_right _ _

theorem pairDeg_add_le (u v : PairRing σ) : pairDeg (u + v) ≤ max (pairDeg u) (pairDeg v) := by
  have h1 := totalDegree_add u.re v.re
  have h2 := totalDegree_add u.im v.im
  simp only [pairDeg, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] at *
  omega

theorem pairDeg_neg (u : PairRing σ) : pairDeg (-u) = pairDeg u := by
  simp only [pairDeg, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, totalDegree_neg]

theorem pairDeg_sub_le (u v : PairRing σ) : pairDeg (u - v) ≤ max (pairDeg u) (pairDeg v) := by
  have h1 := totalDegree_sub u.re v.re
  have h2 := totalDegree_sub u.im v.im
  simp only [pairDeg, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub] at *
  omega

theorem pairDeg_mul_le (u v : PairRing σ) : pairDeg (u * v) ≤ pairDeg u + pairDeg v := by
  have h2 : ∀ f g : MvPolynomial σ ℤ, (2 * f * g).totalDegree ≤ f.totalDegree + g.totalDegree :=
    fun f g => by
      refine (totalDegree_mul _ _).trans (Nat.add_le_add_right ?_ _)
      refine (totalDegree_mul _ _).trans ?_
      rw [← map_ofNat C 2, totalDegree_C, zero_add]
  have hre : (u * v).re.totalDegree ≤ pairDeg u + pairDeg v := by
    rw [QuadraticAlgebra.re_mul]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
    · exact (h2 _ _).trans (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))
  have him : (u * v).im.totalDegree ≤ pairDeg u + pairDeg v := by
    rw [QuadraticAlgebra.im_mul, zero_mul, zero_mul, add_zero]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (Nat.add_le_add (le_max_left _ _) (le_max_right _ _))
    · exact (totalDegree_mul _ _).trans (Nat.add_le_add (le_max_right _ _) (le_max_left _ _))
  exact max_le hre him

theorem pairDeg_one : pairDeg (1 : PairRing σ) = 0 := by
  simp [pairDeg, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem pairDeg_pow_le (u : PairRing σ) (k : ℕ) : pairDeg (u ^ k) ≤ k * pairDeg u := by
  induction k with
  | zero => rw [pow_zero, pairDeg_one, zero_mul]
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (pairDeg_mul_le _ _).trans (Nat.add_le_add_right ih _)

theorem pairDeg_smul_le (c : ℤ) (u : PairRing σ) : pairDeg (c • u) ≤ pairDeg u := by
  simp only [pairDeg, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul]
  exact max_le_max (totalDegree_smul_le _ _) (totalDegree_smul_le _ _)

theorem pairDeg_intCast_mul_le (c : ℤ) (u : PairRing σ) :
    pairDeg ((c : PairRing σ) * u) ≤ pairDeg u := by
  rw [← zsmul_eq_mul]; exact pairDeg_smul_le c u

/-! ### Constants and variables -/

/-- The constant `e + f s` has norm `|e| + 2|f|`. -/
theorem pairNorm_const (e f : ℤ) : pairNorm (⟨C e, C f⟩ : PairRing σ) = e.natAbs + 2 * f.natAbs := by
  simp only [pairNorm, l1_C]

theorem pairDeg_const (e f : ℤ) : pairDeg (⟨C e, C f⟩ : PairRing σ) = 0 := by
  simp only [pairDeg, totalDegree_C, max_self]

/-- The variable pair `X_i + X_j s` has norm `3`. -/
theorem pairNorm_var (i j : σ) : pairNorm (⟨X i, X j⟩ : PairRing σ) = 3 := by
  simp only [pairNorm, l1_X]

theorem pairDeg_var (i j : σ) : pairDeg (⟨X i, X j⟩ : PairRing σ) = 1 := by
  simp only [pairDeg, totalDegree_X, max_self]

theorem pairNorm_natCast (n : ℕ) : pairNorm (n : PairRing σ) = n := by
  simp only [pairNorm, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, l1_natCast,
    l1_zero, mul_zero, add_zero]

theorem pairNorm_ofNat (n : ℕ) [n.AtLeastTwo] : pairNorm (OfNat.ofNat n : PairRing σ) = n :=
  pairNorm_natCast n

theorem pairDeg_natCast (n : ℕ) : pairDeg (n : PairRing σ) = 0 := by
  simp only [pairDeg, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
    ← map_natCast (C : ℤ →+* MvPolynomial σ ℤ), totalDegree_C, totalDegree_zero, max_self]

theorem pairDeg_ofNat (n : ℕ) [n.AtLeastTwo] : pairDeg (OfNat.ofNat n : PairRing σ) = 0 :=
  pairDeg_natCast n

/-- **The weighted pair norm.** (1) subadditivity under sums and differences and homogeneity;
(2) submultiplicativity and powers; (3) degrees of sums and products; (4) the components are
bounded by the pair norm; (5) the constant `e + f s` has norm `|e| + 2|f|` and degree `0`, and
the variable pair `X_i + X_j s`, `i ≠ j`, has norm `3` and degree `1`. -/
theorem pair_norm_estimates (u u' : PairRing σ) (c : ℤ) (k : ℕ) (e f : ℤ) (i j : σ)
    (_hij : i ≠ j) :
    (pairNorm (u + u') ≤ pairNorm u + pairNorm u' ∧ pairNorm (u - u') ≤ pairNorm u + pairNorm u' ∧
      pairNorm (c • u) = c.natAbs * pairNorm u) ∧
    (pairNorm (u * u') ≤ pairNorm u * pairNorm u' ∧ pairNorm (u ^ k) ≤ pairNorm u ^ k) ∧
    (pairDeg (u + u') ≤ max (pairDeg u) (pairDeg u') ∧ pairDeg (u * u') ≤ pairDeg u + pairDeg u') ∧
    (l1 u.re ≤ pairNorm u ∧ l1 u.im ≤ pairNorm u) ∧
    (pairNorm (⟨C e, C f⟩ : PairRing σ) = e.natAbs + 2 * f.natAbs ∧
      pairDeg (⟨C e, C f⟩ : PairRing σ) = 0 ∧
      pairNorm (⟨X i, X j⟩ : PairRing σ) = 3 ∧ pairDeg (⟨X i, X j⟩ : PairRing σ) = 1) :=
  ⟨⟨pairNorm_add_le u u', pairNorm_sub_le u u', pairNorm_smul c u⟩,
    ⟨pairNorm_mul_le u u', pairNorm_pow_le u k⟩, ⟨pairDeg_add_le u u', pairDeg_mul_le u u'⟩,
    ⟨l1_re_le_pairNorm u, l1_im_le_pairNorm u⟩,
    ⟨pairNorm_const e f, pairDeg_const e f, pairNorm_var i j, pairDeg_var i j⟩⟩

end ZInQ.Size
