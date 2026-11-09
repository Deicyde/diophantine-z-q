import ZInQ.AlphaCore
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The alpha sequence

Blueprint: `compiler/natural/exponential/alpha-sequence.md`.

The alpha sequence `U_n = α_b(n)` (`U₀ = 0`, `U₁ = 1`, `U_{n+2} = b U_{n+1} - U_n`) is upstream's
`ZInQ.AlphaPower.alphaZ : ℕ → ℕ → ℤ`, with the defining equations `alphaZ_zero`, `alphaZ_one`,
`alphaZ_add_two` and the Chebyshev correspondence `alphaZ_eq_rescaledChebyshev`. This module
adds the driving matrix `M_b` and the extension to integer indices by `U_{-j} = -U_j`.
-/

namespace ZInQ.AlphaPower

/-- The matrix `M_b = !![b, -1; 1, 0]` driving the alpha recurrence. -/
def alphaMat (b : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(b : ℤ), -1; 1, 0]

open Matrix in
/-- `M_b (U_n, U_{n-1})ᵀ = (U_{n+1}, U_n)ᵀ` for `n ≥ 1` (written with `n + 1` for `n`). -/
theorem alphaMat_mulVec (b n : ℕ) :
    alphaMat b *ᵥ ![alphaZ b (n + 1), alphaZ b n] = ![alphaZ b (n + 2), alphaZ b (n + 1)] := by
  ext i
  fin_cases i <;> simp [alphaMat, alphaZ_add_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The alpha sequence at integer indices: `U_{-j} = -U_j`. -/
def alphaInt (b : ℕ) (n : ℤ) : ℤ :=
  if 0 ≤ n then alphaZ b n.toNat else -alphaZ b (-n).toNat

@[simp] theorem alphaInt_natCast (b n : ℕ) : alphaInt b n = alphaZ b n := by
  simp [alphaInt]

theorem alphaInt_neg (b : ℕ) (n : ℤ) : alphaInt b (-n) = -alphaInt b n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [alphaInt, alphaZ_zero]
    · simp [alphaInt]; omega
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [alphaInt, alphaZ_zero]
    · simp [alphaInt]; omega

/-- The extension is consistent with the recurrence at every integer index. -/
theorem alphaInt_add_two (b : ℕ) (n : ℤ) :
    alphaInt b (n + 2) = (b : ℤ) * alphaInt b (n + 1) - alphaInt b n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · have h1 : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    have h2 : ((k : ℤ) + 2) = ((k + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, h2, alphaInt_natCast, alphaInt_natCast, alphaInt_natCast, alphaZ_add_two]
  · match k with
    | 0 =>
      simp only [Nat.cast_zero, neg_zero, zero_add]
      have h2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
      have h1 : (1 : ℤ) = ((1 : ℕ) : ℤ) := rfl
      rw [h2, h1, alphaInt_natCast, alphaInt_natCast, show ((0 : ℤ)) = ((0 : ℕ) : ℤ) from rfl,
        alphaInt_natCast, alphaZ_add_two]
    | 1 =>
      have e0 : -((1 : ℕ) : ℤ) + 2 = ((1 : ℕ) : ℤ) := by norm_num
      have e1 : -((1 : ℕ) : ℤ) + 1 = ((0 : ℕ) : ℤ) := by norm_num
      rw [e0, e1, alphaInt_neg, alphaInt_natCast, alphaInt_natCast, alphaZ_zero]
      ring
    | j + 2 =>
      have e0 : -((j + 2 : ℕ) : ℤ) + 2 = -((j : ℕ) : ℤ) := by push_cast; ring
      have e1 : -((j + 2 : ℕ) : ℤ) + 1 = -((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e0, e1, alphaInt_neg, alphaInt_neg, alphaInt_neg, alphaInt_natCast, alphaInt_natCast,
        alphaInt_natCast, alphaZ_add_two]
      ring

end ZInQ.AlphaPower
