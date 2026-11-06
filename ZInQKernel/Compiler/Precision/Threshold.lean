import Mathlib
import ZInQ.PrecisionArithmetic

/-!
# The precision threshold as an integer comparison

Blueprint: `compiler/natural/precision/precision-threshold.md`.

For positive naturals `U, V`, `ε = U/V` and `B ∈ ℕ`:
`4ε < 4^(-B) ↔ 4U·4^B < V ↔ 4^B ≤ ⌊(V-1)/(4U)⌋`. The second equivalence is upstream's
`ZInQ.PrecisionArithmetic.four_mul_pow_lt_iff`.
-/

namespace ZInQ.Compiler.Precision

/-- `4ε < 4^(-B) ↔ 4U·4^B < V`. -/
theorem four_eps_lt_iff_nat (U V B : ℕ) (hV : 0 < V) :
    4 * ((U : ℚ) / V) < ((4 : ℚ) ^ B)⁻¹ ↔ 4 * U * 4 ^ B < V := by
  have hV' : (0 : ℚ) < V := by exact_mod_cast hV
  have h4 : (0 : ℚ) < 4 ^ B := by positivity
  rw [← one_div, lt_div_iff₀ h4, mul_div_assoc', div_mul_eq_mul_div, div_lt_one hV']
  exact_mod_cast Iff.rfl

/-- The precision threshold `4ε < 4^(-B) ↔ 4^B ≤ ⌊(V-1)/(4U)⌋`. -/
theorem four_eps_lt_iff (U V B : ℕ) (hU : 0 < U) (hV : 0 < V) :
    4 * ((U : ℚ) / V) < ((4 : ℚ) ^ B)⁻¹ ↔ 4 ^ B ≤ (V - 1) / (4 * U) := by
  rw [four_eps_lt_iff_nat U V B hV]
  exact PrecisionArithmetic.four_mul_pow_lt_iff U V B hU hV

/-- The form used in the precision relation: `4ε · 4^B < 1 ↔ 4^B ≤ ⌊(V-1)/(4U)⌋`. -/
theorem four_eps_mul_pow_lt_one_iff (U V B : ℕ) (hU : 0 < U) (hV : 0 < V) :
    4 * ((U : ℚ) / V) * 4 ^ B < 1 ↔ 4 ^ B ≤ (V - 1) / (4 * U) := by
  rw [← four_eps_lt_iff U V B hU hV, ← lt_div_iff₀ (by positivity), one_div]

end ZInQ.Compiler.Precision
