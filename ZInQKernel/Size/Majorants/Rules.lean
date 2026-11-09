import ZInQKernel.Size.Majorants.Basic

/-!
# Closure rules for the height majorant

Blueprint: `size/majorants/majorant-rules.md`.

For `B ≥ 2^20`:

0. monotonicity, variables at height `0`, constants `|c| ≤ 2^(B^8)` at height `1`
   (`Maj.mono`, `Maj.X`, `Maj.C`);
1. sums and products at height `1 + max(h₁, h₂)` (`Maj.add`, `Maj.mul`);
2. substitution at height `H + k + 1` (`Maj.bind₁`);
3. constructors (`deg C ≤ B^4`, `‖C‖₁ ≤ 2^(B^8)`) at height `k + 1` (`Maj.constructor`);
4. renaming keeps the height (`Maj.rename`); more generally so does the substitution of
   polynomials of degree and norm at most `1`, such as variables and `0`
   (`Maj.bind₁_of_maj_zero`);
5. sums of at most `B` squares at height `h + 2` (`Maj.sum_sq`);
6. products of at most `B` factors at height `h + 1` (`Maj.prod`).

The proofs go through the finer scale `Scale` of `ZInQKernel.Size.Majorants.Basic`, except for
the constructor rule, whose norm and degree bounds are not of the same size.
-/

namespace ZInQ.Size

open MvPolynomial ZInQ.Syntax

variable {σ τ : Type*} {B : ℕ}

theorem one_le_of_two_pow_twenty_le (hB : 2 ^ 20 ≤ B) : 1 ≤ B := le_trans (by norm_num) hB

namespace Maj

/-! ### Rule 0: monotonicity and atoms -/

theorem mono {h h' : ℕ} {P : MvPolynomial σ ℤ} (hP : Maj B h P) (hh : h ≤ h') (hB : 1 ≤ B) :
    Maj B h' P := by
  rcases Nat.eq_zero_or_pos h' with rfl | hh'
  · obtain rfl : h = 0 := by omega
    exact hP
  · exact Scale.maj ((Maj.sz hP).mono hB (by omega) le_rfl) hh'.ne'

theorem X (i : σ) : Maj B 0 (X i : MvPolynomial σ ℤ) := by
  rw [maj_zero_iff, totalDegree_X, l1_X]
  exact ⟨le_rfl, le_rfl⟩

theorem zero (h : ℕ) (hB : 1 ≤ B) : Maj B h (0 : MvPolynomial σ ℤ) :=
  mono (h := 0) (by rw [maj_zero_iff]; simp) (Nat.zero_le h) hB

theorem C {c : ℤ} (hc : c.natAbs ≤ 2 ^ B ^ 8) : Maj B 1 (MvPolynomial.C c : MvPolynomial σ ℤ) := by
  rw [maj_iff_of_ne_zero one_ne_zero, totalDegree_C, l1_C]
  exact ⟨Nat.zero_le _, hc⟩

/-! ### Rule 1: operations -/

theorem add {h₁ h₂ : ℕ} {P Q : MvPolynomial σ ℤ} (hB : 2 ^ 20 ≤ B) (hP : Maj B h₁ P)
    (hQ : Maj B h₂ Q) : Maj B (1 + max h₁ h₂) (P + Q) := by
  have hB1 := one_le_of_two_pow_twenty_le hB
  have h := ((Maj.sz hP).mono hB1 (Nat.mul_le_mul_left 8 (le_max_left h₁ h₂)) le_rfl).add
    ((Maj.sz hQ).mono hB1 (Nat.mul_le_mul_left 8 (le_max_right h₁ h₂)) le_rfl) hB1
  rw [add_comm]
  exact h.maj_succ (two_pow_le_pow_eight hB (by norm_num))

theorem mul {h₁ h₂ : ℕ} {P Q : MvPolynomial σ ℤ} (hB : 2 ^ 20 ≤ B) (hP : Maj B h₁ P)
    (hQ : Maj B h₂ Q) : Maj B (1 + max h₁ h₂) (P * Q) := by
  have hB1 := one_le_of_two_pow_twenty_le hB
  have h := ((Maj.sz hP).mono hB1 (Nat.mul_le_mul_left 8 (le_max_left h₁ h₂)) le_rfl).mul
    ((Maj.sz hQ).mono hB1 (Nat.mul_le_mul_left 8 (le_max_right h₁ h₂)) le_rfl)
  rw [add_comm]
  exact h.maj_succ (two_pow_le_pow_eight hB (by norm_num))

/-! ### Rule 2: substitution -/

theorem bind₁ {H k : ℕ} {P : MvPolynomial σ ℤ} {Q : σ → MvPolynomial τ ℤ} (hB : 2 ^ 20 ≤ B)
    (hP : Maj B H P) (hQ : ∀ i ∈ P.vars, Maj B k (Q i)) :
    Maj B (H + k + 1) (MvPolynomial.bind₁ Q P) := by
  have hB1 := one_le_of_two_pow_twenty_le hB
  have h := (Maj.sz hP).bind₁ (fun i hi => Maj.sz (hQ i hi)) hB1
  rw [← mul_add] at h
  exact h.maj_succ (two_pow_le_pow_eight hB (by norm_num))

/-! ### Rule 3: constructors -/

theorem constructor {k : ℕ} {C : MvPolynomial σ ℤ} {Q : σ → MvPolynomial τ ℤ} (hB : 2 ^ 20 ≤ B)
    (hdeg : C.totalDegree ≤ B ^ 4) (hl1 : l1 C ≤ 2 ^ B ^ 8) (hQ : ∀ i ∈ C.vars, Maj B k (Q i)) :
    Maj B (k + 1) (MvPolynomial.bind₁ Q C) := by
  have hB1 := one_le_of_two_pow_twenty_le hB
  have hB4 : 2 ≤ B ^ 4 := (two_pow_le_pow_four hB (s := 1) (by norm_num)).trans_eq' rfl
  rw [maj_iff_of_ne_zero (Nat.succ_ne_zero k)]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hQ' : ∀ i ∈ C.vars, (Q i).totalDegree ≤ 1 ∧ l1 (Q i) ≤ 1 := fun i hi =>
      maj_zero_iff.1 (hQ i hi)
    refine ⟨(Syntax.totalDegree_bind₁_le Q C 1 fun i hi => (hQ' i hi).1).trans ?_, ?_⟩
    · rw [mul_one]
      exact hdeg.trans (Nat.pow_le_pow_right hB1 (by norm_num))
    · refine (l1_bind₁_le Q C le_rfl fun i hi => (hQ' i hi).2).trans ?_
      rw [one_pow, mul_one]
      simpa using hl1
  · have hQ' : ∀ i ∈ C.vars, (Q i).totalDegree ≤ B ^ (8 * k) ∧ l1 (Q i) ≤ 2 ^ B ^ (8 * k) :=
      fun i hi => (maj_iff_of_ne_zero hk.ne').1 (hQ i hi)
    have hpow : B ^ (8 * (k + 1)) = B ^ 4 * B ^ (8 * k + 4) := by
      rw [← pow_add]; congr 1; ring
    have hpow' : B ^ (8 * k + 4) = B ^ 4 * B ^ (8 * k) := by rw [← pow_add]; congr 1; ring
    have h8 : B ^ 8 ≤ B ^ (8 * k + 4) := Nat.pow_le_pow_right hB1 (by omega)
    refine ⟨(Syntax.totalDegree_bind₁_le Q C _ fun i hi => (hQ' i hi).1).trans ?_, ?_⟩
    · rw [hpow, hpow']
      calc C.totalDegree * B ^ (8 * k) ≤ B ^ 4 * B ^ (8 * k) := Nat.mul_le_mul_right _ hdeg
        _ ≤ B ^ 4 * (B ^ 4 * B ^ (8 * k)) := Nat.le_mul_of_pos_left _ (by positivity)
    · refine (l1_bind₁_le Q C Nat.one_le_two_pow fun i hi => (hQ' i hi).2).trans ?_
      refine (Nat.mul_le_mul hl1 (Nat.pow_le_pow_right (by norm_num) hdeg)).trans ?_
      rw [← pow_mul, ← pow_add]
      refine Nat.pow_le_pow_right (by norm_num) ?_
      rw [hpow, mul_comm (B ^ (8 * k)) (B ^ 4), ← hpow']
      calc B ^ 8 + B ^ (8 * k + 4) ≤ 2 * B ^ (8 * k + 4) := by omega
        _ ≤ B ^ 4 * B ^ (8 * k + 4) := Nat.mul_le_mul_right _ hB4

/-! ### Rule 4: renaming -/

theorem rename {h : ℕ} {P : MvPolynomial σ ℤ} (f : σ → τ) (hP : Maj B h P) :
    Maj B h (MvPolynomial.rename f P) := by
  have hd := totalDegree_rename_le f P
  have hn := l1_rename_le f P
  unfold Maj at hP ⊢
  split_ifs at hP ⊢
  · exact ⟨hd.trans hP.1, hn.trans hP.2⟩
  · exact ⟨hd.trans hP.1, hn.trans hP.2⟩

/-- Substituting polynomials of degree and norm at most `1` (variables, `0`, `±1`) keeps the
height. -/
theorem bind₁_of_maj_zero {h : ℕ} {P : MvPolynomial σ ℤ} {Q : σ → MvPolynomial τ ℤ}
    (hP : Maj B h P) (hQ : ∀ i ∈ P.vars, Maj B 0 (Q i)) :
    Maj B h (MvPolynomial.bind₁ Q P) := by
  have hQ' : ∀ i ∈ P.vars, (Q i).totalDegree ≤ 1 ∧ l1 (Q i) ≤ 1 := fun i hi =>
    maj_zero_iff.1 (hQ i hi)
  have hd : (MvPolynomial.bind₁ Q P).totalDegree ≤ P.totalDegree := by
    simpa using Syntax.totalDegree_bind₁_le Q P 1 fun i hi => (hQ' i hi).1
  have hn : l1 (MvPolynomial.bind₁ Q P) ≤ l1 P := by
    simpa using l1_bind₁_le Q P le_rfl fun i hi => (hQ' i hi).2
  unfold Maj at hP ⊢
  split_ifs at hP ⊢
  · exact ⟨hd.trans hP.1, hn.trans hP.2⟩
  · exact ⟨hd.trans hP.1, hn.trans hP.2⟩

/-! ### Rules 5 and 6: sums of squares and products -/

theorem sum_sq {h : ℕ} (hB : 2 ^ 20 ≤ B) (cs : List (MvPolynomial σ ℤ)) (hlen : cs.length ≤ B)
    (hc : ∀ c ∈ cs, Maj B h c) : Maj B (h + 2) (cs.map (· ^ 2)).sum := by
  have hB1 := one_le_of_two_pow_twenty_le hB
  have hsq : ∀ f ∈ cs.map (· ^ 2), Scale B (8 * (h + 1)) 0 f := by
    intro f hf
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hf
    have := ((Maj.sz (hc c hc')).pow (n := 2) (k := 1) (by norm_num)).lift
      (two_pow_le_pow_eight hB (s := 0 + 1) (by norm_num))
    simpa [Nat.mul_succ] using this
  have hlen' : (cs.map (· ^ 2)).length ≤ 2 ^ (2 ^ 0 * B ^ (8 * (h + 1))) := by
    rw [List.length_map, pow_zero, one_mul]
    refine hlen.trans ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) ?_))
    exact Nat.le_self_pow (by omega) B
  exact (Scale.list_sum hsq hlen' hB1).maj_succ (two_pow_le_pow_eight hB (by norm_num))

theorem prod {h : ℕ} (hB : 2 ^ 20 ≤ B) (cs : List (MvPolynomial σ ℤ)) (hlen : cs.length ≤ B)
    (hc : ∀ c ∈ cs, Maj B h c) : Maj B (h + 1) cs.prod := by
  have hB1 := one_le_of_two_pow_twenty_le hB
  have := Scale.list_prod_of_le_pow (fun c hc' => Maj.sz (hc c hc')) (d := 1) (by simpa using hlen)
  refine Scale.maj (this.mono hB1 (by omega) le_rfl) (Nat.succ_ne_zero h)

end Maj

end ZInQ.Size
