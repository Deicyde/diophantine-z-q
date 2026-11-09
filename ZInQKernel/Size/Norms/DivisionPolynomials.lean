import ZInQKernel.Size.Norms.Pair
import ZInQKernel.Model.DivisionPolynomials.Defs

/-!
# Size of the division polynomials

Blueprint: `size/norms/division-polynomial-size.md`.

In `S[s]`, `S = ℤ[x₀, x₁, y₀, y₁]`, with `x = x₀ + x₁ s` (`compX`), `y = y₀ + y₁ s` (`compY`) and
`A = -11243 + 7950 s` (`ZInQ.Syntax.componentA`), the values `F_n = f_n(x)` of the normalized
division polynomials (`divF`) satisfy `deg F_n ≤ (n + 1)³` and `‖F_n‖ ≤ 2^{100 (n+1)³}`
(`divF_size`), by strong induction on `n` from the recurrences `normDiv_even` and `normDiv_odd`;
the polynomials are never expanded at a large index. Consequently the component polynomials
satisfy `deg Ψ_{n,c} ≤ 2(|n| + 1)³` and `‖Ψ_{n,c}‖₁ ≤ 2^{101 (|n|+1)³}` (`psiComponent_size`).

Sizes are tracked by the predicate `Sz u d e : pairDeg u ≤ d ∧ pairNorm u ≤ 2^e`.
-/

namespace ZInQ.Size

open ZInQ.Syntax (l1 l1_neg l1_zero normDiv componentA ComponentRing psiComponent psiEval
  psiEval_eq divD0 normDiv_even normDiv_odd normDiv_three normDiv_four)

variable {σ : Type*}

/-! ### The size predicate -/

/-- `u` has degree at most `d` and norm at most `2^e`. -/
def Sz (u : PairRing σ) (d e : ℕ) : Prop := pairDeg u ≤ d ∧ pairNorm u ≤ 2 ^ e

namespace Sz

variable {u v : PairRing σ} {d d' e e' : ℕ}

theorem mono (h : Sz u d e) {d₁ e₁ : ℕ} (hd : d ≤ d₁) (he : e ≤ e₁) : Sz u d₁ e₁ :=
  ⟨h.1.trans hd, h.2.trans (Nat.pow_le_pow_right (by norm_num) he)⟩

theorem mul (h : Sz u d e) (h' : Sz v d' e') : Sz (u * v) (d + d') (e + e') :=
  ⟨(pairDeg_mul_le u v).trans (Nat.add_le_add h.1 h'.1),
    (pairNorm_mul_le u v).trans ((Nat.mul_le_mul h.2 h'.2).trans_eq (pow_add 2 e e').symm)⟩

theorem pow (h : Sz u d e) (k : ℕ) : Sz (u ^ k) (k * d) (k * e) := by
  refine ⟨(pairDeg_pow_le u k).trans (Nat.mul_le_mul_left k h.1), (pairNorm_pow_le u k).trans ?_⟩
  rw [mul_comm k e, pow_mul]
  exact Nat.pow_le_pow_left h.2 k

private theorem two_pow_add_le (e e' : ℕ) : 2 ^ e + 2 ^ e' ≤ 2 ^ (max e e' + 1) := by
  have h1 : 2 ^ e ≤ 2 ^ max e e' := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have h2 : 2 ^ e' ≤ 2 ^ max e e' := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  rw [pow_succ]
  omega

theorem add (h : Sz u d e) (h' : Sz v d' e') : Sz (u + v) (max d d') (max e e' + 1) :=
  ⟨(pairDeg_add_le u v).trans (max_le_max h.1 h'.1),
    (pairNorm_add_le u v).trans ((Nat.add_le_add h.2 h'.2).trans (two_pow_add_le e e'))⟩

theorem sub (h : Sz u d e) (h' : Sz v d' e') : Sz (u - v) (max d d') (max e e' + 1) :=
  ⟨(pairDeg_sub_le u v).trans (max_le_max h.1 h'.1),
    (pairNorm_sub_le u v).trans ((Nat.add_le_add h.2 h'.2).trans (two_pow_add_le e e'))⟩

theorem intCast_mul (c : ℤ) (hc : c.natAbs ≤ 1) (h : Sz u d e) : Sz ((c : PairRing σ) * u) d e := by
  refine ⟨(pairDeg_intCast_mul_le c u).trans h.1, ?_⟩
  rw [pairNorm_intCast_mul]
  exact (Nat.mul_le_mul hc h.2).trans_eq (one_mul _)

theorem zero : Sz (0 : PairRing σ) 0 0 := by
  refine ⟨?_, ?_⟩ <;> simp [pairDeg, pairNorm]

theorem one : Sz (1 : PairRing σ) 0 0 := by
  rw [Sz, pairDeg_one, pairNorm_one]; simp

theorem ofNat (n : ℕ) [n.AtLeastTwo] (h : n ≤ 2 ^ e) : Sz (OfNat.ofNat n : PairRing σ) 0 e := by
  rw [Sz, pairDeg_ofNat, pairNorm_ofNat]; exact ⟨le_rfl, h⟩

end Sz

/-! ### The generic point and the coefficient -/

/-- `x = x₀ + x₁ s`. -/
noncomputable def compX : ComponentRing := ⟨.X 0, .X 1⟩

/-- `y = y₀ + y₁ s`. -/
noncomputable def compY : ComponentRing := ⟨.X 2, .X 3⟩

theorem Sz_compX : Sz compX 1 2 := by
  rw [Sz, compX, pairDeg_var, pairNorm_var]; norm_num

theorem Sz_compY : Sz compY 1 2 := by
  rw [Sz, compY, pairDeg_var, pairNorm_var]; norm_num

/-- `‖A‖ = 11243 + 2 · 7950 = 27143 < 2^15`. -/
theorem pairNorm_componentA : pairNorm componentA = 27143 := by
  simp only [componentA, pairNorm, l1_neg]
  show l1 (11243 : MvPolynomial (Fin 4) ℤ) + 2 * l1 (7950 : MvPolynomial (Fin 4) ℤ) = 27143
  rw [l1_ofNat, l1_ofNat]

theorem Sz_componentA : Sz componentA 0 15 := by
  refine ⟨?_, ?_⟩
  · simp only [componentA, pairDeg, MvPolynomial.totalDegree_neg,
      ← map_ofNat (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 4) ℤ), MvPolynomial.totalDegree_C,
      max_self, le_refl]
  · rw [pairNorm_componentA]; norm_num

/-! ### The values `F_n = f_n(x)` -/

/-- `F_n = f_n(x)` for the normalized division polynomial `f_n` of `y² = x³ + Ax`. -/
noncomputable def divF (n : ℕ) : ComponentRing := (normDiv componentA n).eval compX

/-- `D₀ = 16(x³ + Ax)²` has degree `6` and norm at most `2^40`. -/
theorem Sz_divD0 : Sz ((divD0 componentA).eval compX) 6 40 := by
  simp only [divD0, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  exact ((Sz.ofNat 16 (e := 4) (by norm_num)).mul
    (((Sz_compX.pow 3).add (Sz_componentA.mul Sz_compX)).pow 2)).mono (by norm_num) (by norm_num)

theorem divF_three_size : Sz (divF 3) 64 6400 := by
  simp only [divF, normDiv_three, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  exact (((((Sz.ofNat 3 (e := 2) (by norm_num)).mul (Sz_compX.pow 4)).add
    (((Sz.ofNat 6 (e := 3) (by norm_num)).mul Sz_componentA).mul (Sz_compX.pow 2))).sub
    (Sz_componentA.pow 2))).mono (by norm_num) (by norm_num)

theorem divF_four_size : Sz (divF 4) 125 12500 := by
  simp only [divF, normDiv_four, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  have h5 : Sz (5 : ComponentRing) 0 3 := Sz.ofNat 5 (by norm_num)
  exact ((Sz.ofNat 2 (e := 1) (by norm_num)).mul
    ((((Sz_compX.pow 6).add ((h5.mul Sz_componentA).mul (Sz_compX.pow 4))).sub
      ((h5.mul (Sz_componentA.pow 2)).mul (Sz_compX.pow 2))).sub
      (Sz_componentA.pow 3))).mono (by norm_num) (by norm_num)

private theorem add_max_le {a b c D : ℕ} (h1 : a + b ≤ D) (h2 : a + c ≤ D) : a + max b c ≤ D := by
  rcases le_total b c with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1

private theorem add_max_succ_le {a b c D : ℕ} (h1 : a + b + 1 ≤ D) (h2 : a + c + 1 ≤ D) :
    a + (max b c + 1) ≤ D := by
  rw [← add_assoc]; exact Nat.succ_le_of_lt (Nat.lt_of_succ_le (by
    rcases le_total b c with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1))

private theorem max_succ_le {b c D : ℕ} (h1 : b + 1 ≤ D) (h2 : c + 1 ≤ D) : max b c + 1 ≤ D := by
  rcases le_total b c with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1

/-- **Size of the division polynomials.** `deg F_n ≤ (n + 1)³` and `‖F_n‖ ≤ 2^{100 (n+1)³}`. -/
theorem divF_size (n : ℕ) : Sz (divF n) ((n + 1) ^ 3) (100 * (n + 1) ^ 3) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n, ih with
  | 0, _ => simpa [divF] using (Sz.zero (σ := Fin 4)).mono (Nat.zero_le 1) (Nat.zero_le 100)
  | 1, _ => simpa [divF] using (Sz.one (σ := Fin 4)).mono (Nat.zero_le 8) (Nat.zero_le 800)
  | 2, _ => simpa [divF] using (Sz.one (σ := Fin 4)).mono (Nat.zero_le 27) (Nat.zero_le 2700)
  | 3, _ => exact divF_three_size
  | 4, _ => exact divF_four_size
  | n + 5, ih =>
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' (n + 5)
    · -- even step, `n + 5 = 2m`, `m = k + 3`
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      rw [hm]
      have e := congrArg (Polynomial.eval compX) (normDiv_even componentA (m := k + 3) (by omega))
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
        show k + 3 + 2 = k + 5 by ring, show k + 3 - 1 = k + 2 by omega,
        show k + 3 - 2 = k + 1 by omega, show k + 3 + 1 = k + 4 by ring] at e
      rw [divF, e]
      have h3 := ih (k + 3) (by omega)
      have h5 := ih (k + 5) (by omega)
      have h2 := ih (k + 2) (by omega)
      have h1 := ih (k + 1) (by omega)
      have h4 := ih (k + 4) (by omega)
      have i1 : (k + 3 + 1) ^ 3 + ((k + 5 + 1) ^ 3 + 2 * (k + 2 + 1) ^ 3) + 9 ≤
          (2 * (k + 3) + 1) ^ 3 := by
        nlinarith [Nat.zero_le (k ^ 3), Nat.zero_le (k ^ 2), Nat.zero_le k]
      have i2 : (k + 3 + 1) ^ 3 + ((k + 1 + 1) ^ 3 + 2 * (k + 4 + 1) ^ 3) + 9 ≤
          (2 * (k + 3) + 1) ^ 3 := by
        nlinarith [Nat.zero_le (k ^ 3), Nat.zero_le (k ^ 2), Nat.zero_le k]
      refine (h3.mul ((h5.mul (h2.pow 2)).sub (h1.mul (h4.pow 2)))).mono ?_ ?_
      · exact add_max_le (by omega) (by omega)
      · exact add_max_succ_le (by omega) (by omega)
    · -- odd step, `n + 5 = 2m + 1`, `m = k + 2`
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      rw [hm]
      have e := congrArg (Polynomial.eval compX) (normDiv_odd componentA (m := k + 2) (by omega))
      simp only [apply_ite (Polynomial.eval compX), Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_pow, show k + 2 + 2 = k + 4 by ring, show k + 2 - 1 = k + 1 by omega,
        show k + 2 + 1 = k + 3 by ring] at e
      rw [divF, e]
      have h4 := ih (k + 4) (by omega)
      have h2 := ih (k + 2) (by omega)
      have h1 := ih (k + 1) (by omega)
      have h3 := ih (k + 3) (by omega)
      have hL := h4.mul (h2.pow 3)
      have hR := h1.mul (h3.pow 3)
      have iL : (k + 4 + 1) ^ 3 + 3 * (k + 2 + 1) ^ 3 + 10 ≤ (2 * (k + 2) + 1 + 1) ^ 3 := by
        nlinarith [Nat.zero_le (k ^ 3), Nat.zero_le (k ^ 2), Nat.zero_le k]
      have iR : (k + 1 + 1) ^ 3 + 3 * (k + 3 + 1) ^ 3 + 16 ≤ (2 * (k + 2) + 1 + 1) ^ 3 := by
        nlinarith [Nat.zero_le (k ^ 3), Nat.zero_le (k ^ 2), Nat.zero_le k]
      split_ifs
      · refine ((Sz_divD0.mul hL).sub hR).mono ?_ ?_
        · exact max_le (by omega) (by omega)
        · exact max_succ_le (by omega) (by omega)
      · refine (hL.sub (Sz_divD0.mul hR)).mono ?_ ?_
        · exact max_le (by omega) (by omega)
        · exact max_succ_le (by omega) (by omega)

/-- **Size of the division polynomials**, unfolded: `deg F_n ≤ (n + 1)³` and
`‖F_n‖ ≤ 2^{100 (n+1)³}` for `F_n = f_n(x₀ + x₁ s)`. -/
theorem normDiv_size (n : ℕ) :
    pairDeg ((normDiv componentA n).eval compX) ≤ (n + 1) ^ 3 ∧
      pairNorm ((normDiv componentA n).eval compX) ≤ 2 ^ (100 * (n + 1) ^ 3) :=
  divF_size n

/-- The pair `ψ_n(x, y)` for `n ≠ 0` has degree at most `(|n| + 1)³ + 1` and norm at most
`2^{100 (|n|+1)³ + 3}`. -/
theorem psiEval_size (n : ℤ) :
    Sz (psiEval componentA n compX compY) ((n.natAbs + 1) ^ 3 + 1)
      (100 * (n.natAbs + 1) ^ 3 + 3) := by
  rw [psiEval_eq]
  refine Sz.intCast_mul _ ?_ ((divF_size n.natAbs).mul ?_)
  · rcases Int.sign_trichotomy n with h | h | h <;> rw [h] <;> decide
  · split_ifs
    · exact (Sz.ofNat 2 (e := 1) (by norm_num)).mul Sz_compY
    · exact Sz.one.mono (Nat.zero_le _) (Nat.zero_le _)

theorem psiEval_zero : psiEval componentA 0 compX compY = 0 := by
  rw [psiEval_eq]; simp

/-- **Size of the component polynomials.** For `n ∈ ℤ` and `c ∈ {0, 1}`,
`deg Ψ_{n,c} ≤ 2(|n| + 1)³` and `‖Ψ_{n,c}‖₁ ≤ 2^{101 (|n|+1)³}`. -/
theorem psiComponent_size (n : ℤ) (c : Fin 2) :
    (psiComponent n c).totalDegree ≤ 2 * (n.natAbs + 1) ^ 3 ∧
      l1 (psiComponent n c) ≤ 2 ^ (101 * (n.natAbs + 1) ^ 3) := by
  have hv : psiComponent n c = ![(psiEval componentA n compX compY).re,
      (psiEval componentA n compX compY).im] c := rfl
  rcases eq_or_ne n 0 with rfl | hn
  · rw [hv, psiEval_zero]
    fin_cases c <;> simp
  · obtain ⟨hd, hN⟩ := psiEval_size n
    have hK : 8 ≤ (n.natAbs + 1) ^ 3 := by
      have : 2 ≤ n.natAbs + 1 := by have := Int.natAbs_pos.2 hn; omega
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_left this 3
    have hd' : pairDeg (psiEval componentA n compX compY) ≤ 2 * (n.natAbs + 1) ^ 3 := by omega
    have hN' : pairNorm (psiEval componentA n compX compY) ≤ 2 ^ (101 * (n.natAbs + 1) ^ 3) :=
      hN.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [hv]
    fin_cases c
    · exact ⟨(totalDegree_re_le_pairDeg _).trans hd', (l1_re_le_pairNorm _).trans hN'⟩
    · exact ⟨(totalDegree_im_le_pairDeg _).trans hd', (l1_im_le_pairNorm _).trans hN'⟩

end ZInQ.Size
