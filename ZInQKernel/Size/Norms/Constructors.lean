import ZInQKernel.Size.Norms.Guard

/-!
# Uniform bounds for the finite constructors

Blueprint: `size/norms/constructor-bounds.md`.

For an integer `B ≥ 2^20` exceeding the occurring indices and cutoffs, the component
polynomials `Ψ_{n,c}` (`psi_uniform`), the guard polynomials `G_T` (`guard_uniform`) and the
constants `c` of `fixed` nodes (`const_uniform`) have degree at most `B⁴` and norm at most
`2^{B⁸}`.
-/

namespace ZInQ.Size

open MvPolynomial
open ZInQ.Syntax (l1 l1_C psiComponent guardPoly)

variable {B : ℕ}

private theorem pow_mono {a b : ℕ} (hab : a ≤ b) (k : ℕ) : a ^ k ≤ b ^ k := Nat.pow_le_pow_left hab k

/-- `c B^k ≤ B^(k+1)` for `c ≤ B`. -/
private theorem mul_pow_le {c k : ℕ} (hc : c ≤ B) : c * B ^ k ≤ B ^ (k + 1) := by
  rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ hc

/-- **Uniform bounds**, item (1): for `|n| + 1 ≤ B` and `c ∈ {0, 1}`,
`deg Ψ_{n,c} ≤ B⁴` and `‖Ψ_{n,c}‖₁ ≤ 2^{B⁸}`. -/
theorem psi_uniform (hB : 2 ^ 20 ≤ B) (n : ℤ) (hn : n.natAbs + 1 ≤ B) (c : Fin 2) :
    (psiComponent n c).totalDegree ≤ B ^ 4 ∧ l1 (psiComponent n c) ≤ 2 ^ B ^ 8 := by
  obtain ⟨hd, hN⟩ := psiComponent_size n c
  have h3 := pow_mono hn 3
  refine ⟨hd.trans ((Nat.mul_le_mul_left 2 h3).trans (mul_pow_le (by omega))), hN.trans ?_⟩
  refine Nat.pow_le_pow_right (by norm_num) ?_
  calc 101 * (n.natAbs + 1) ^ 3 ≤ 101 * B ^ 3 := Nat.mul_le_mul_left _ h3
    _ ≤ B ^ 4 := mul_pow_le (by omega)
    _ ≤ B ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)

/-- **Uniform bounds**, item (2): for `0 ≤ T ≤ B - 1`, `deg G_T ≤ B⁴` and `‖G_T‖₁ ≤ 2^{B⁸}`. -/
theorem guard_uniform (hB : 2 ^ 20 ≤ B) (T : ℤ) (hT0 : 0 ≤ T) (hT : T + 1 ≤ B) :
    (guardPoly T).totalDegree ≤ B ^ 4 ∧ l1 (guardPoly T) ≤ 2 ^ B ^ 8 := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, T = t := ⟨T.toNat, by omega⟩
  have ht : t + 1 ≤ B := by omega
  obtain ⟨hd, hN⟩ := guardPoly_size t
  refine ⟨hd.trans ((Nat.mul_le_mul_left 16 (pow_mono ht 3)).trans (mul_pow_le (by omega))),
    hN.trans (Nat.pow_le_pow_right (by norm_num) ?_)⟩
  have hB2 : 2 ^ 39 ≤ B ^ 2 :=
    calc 2 ^ 39 ≤ (2 ^ 20) ^ 2 := by norm_num
      _ ≤ B ^ 2 := pow_mono hB 2
  calc 2 ^ 39 * (t + 1) ^ 6 ≤ B ^ 2 * B ^ 6 := Nat.mul_le_mul hB2 (pow_mono ht 6)
    _ = B ^ 8 := by ring

/-- **Uniform bounds**, item (3): for `|c| ≤ B - 1`, the constant polynomial `c` has degree
`0 ≤ B⁴` and norm `|c| ≤ 2^{B⁸}`. -/
theorem const_uniform {σ : Type*} (_hB : 2 ^ 20 ≤ B) (c : ℤ) (hc : c.natAbs + 1 ≤ B) :
    (C c : MvPolynomial σ ℤ).totalDegree = 0 ∧ 0 ≤ B ^ 4 ∧
      l1 (C c : MvPolynomial σ ℤ) = c.natAbs ∧ c.natAbs ≤ 2 ^ B ^ 8 := by
  refine ⟨totalDegree_C c, Nat.zero_le _, l1_C c, ?_⟩
  calc c.natAbs ≤ B := by omega
    _ ≤ B ^ 8 := Nat.le_self_pow (by norm_num) B
    _ ≤ 2 ^ B ^ 8 := (Nat.lt_two_pow_self).le

end ZInQ.Size
