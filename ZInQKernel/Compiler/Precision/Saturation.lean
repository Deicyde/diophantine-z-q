import Mathlib
import ZInQ.PrecisionAlgorithms

/-!
# Saturated arithmetic, capped multiplication and binary exponentiation

Blueprint: `compiler/natural/precision/saturated-arithmetic.md` and
`compiler/natural/precision/capped-power.md`.

The saturation `σ_L(x) = min(x, L + 1)` is upstream's `ZInQ.PrecisionArithmetic.saturate`, with
items 1–4 of the saturation statement proved there; item 5 (factorials) is
`saturate_factorial_succ` below. Capped multiplication `cmul_L` and capped binary
exponentiation `cpow_L` are upstream's `ZInQ.PrecisionAlgorithms.cappedMul` and `cappedPower`
(a transcription of `Capped.mul` and `Capped.power` of the reference program, whose loop is
`cappedPowerLoop`, terminating because the exponent halves). The two theorems
`saturatedArithmetic` and `cappedArithmetic` collect the statements of the two articles.
-/

namespace ZInQ.Compiler.Precision

open PrecisionArithmetic PrecisionAlgorithms

/-- Item 5: `σ_L((n+1)!) = σ_L(σ_L(n!) · (n+1))`. -/
theorem saturate_factorial_succ (L n : ℕ) :
    saturate L (n + 1).factorial = saturate L (saturate L n.factorial * (n + 1)) := by
  rw [Nat.factorial_succ, Nat.mul_comm]
  calc saturate L (n.factorial * (n + 1))
      = saturate L (saturate L n.factorial * saturate L (n + 1)) := (saturate_mul ..).symm
    _ = saturate L (saturate L (saturate L n.factorial) * saturate L (n + 1)) := by
        rw [saturate_saturate]
    _ = saturate L (saturate L n.factorial * (n + 1)) := saturate_mul ..

/-- The saturation identities (items 1–5 of the saturated-arithmetic statement). -/
theorem saturatedArithmetic (L : ℕ) :
    (∀ x, saturate L x ≤ L ↔ x ≤ L) ∧ (∀ x k, k ≤ L → (saturate L x ≤ k ↔ x ≤ k)) ∧
    (∀ x, saturate L (saturate L x) = saturate L x) ∧ saturate L 0 = 0 ∧ saturate L 1 = 1 ∧
    (∀ x y, saturate L (saturate L x + saturate L y) = saturate L (x + y)) ∧
    (∀ x y, saturate L (saturate L x * saturate L y) = saturate L (x * y)) ∧
    (∀ x y, saturate L (max (saturate L x) (saturate L y)) = saturate L (max x y)) ∧
    (∀ x n, saturate L (saturate L x ^ n) = saturate L (x ^ n)) ∧
    (1 ≤ L → ∀ x n, saturate L (x ^ saturate L n) = saturate L (x ^ n)) ∧
    (1 ≤ L → ∀ x n, saturate L (saturate L x ^ saturate L n) = saturate L (x ^ n)) ∧
    (∀ n, saturate L (n + 1).factorial = saturate L (saturate L n.factorial * (n + 1))) :=
  ⟨saturate_le_iff L, fun x k hk => saturate_le_iff_of_le L x k hk, saturate_saturate L,
    saturate_zero L, saturate_one L, saturate_add L, saturate_mul L, saturate_max L,
    saturate_pow L, fun hL x n => saturate_pow_saturate_exponent L x n hL,
    fun hL x n => saturate_pow_saturate L x n hL, saturate_factorial_succ L⟩

/-- Capped multiplication and capped binary exponentiation compute the saturated product and
power: `cmul_L(a, b) = σ_L(ab)`, `cpow_L(x, e) = σ_L(x^e)` and `cpow_L(x, e) ≤ L ↔ x^e ≤ L`. -/
theorem cappedArithmetic (L : ℕ) :
    (∀ a b, cappedMul L a b = saturate L (a * b)) ∧
    (∀ x e, cappedPower L x e = saturate L (x ^ e)) ∧
    (∀ x e, cappedPower L x e ≤ L ↔ x ^ e ≤ L) :=
  ⟨cappedMul_eq_saturate L, cappedPower_eq_saturate L, cappedPower_le_iff L⟩

end ZInQ.Compiler.Precision
