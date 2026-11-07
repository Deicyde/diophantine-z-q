import ZInQ.NumericalTowerBounds
import Mathlib

/-!
# Comparison with the towers

Blueprint: `size/majorants/tower-comparison.md`.

The tower `2↑↑n` is `hyperoperation 4 2 n`: `2↑↑0 = 1`, `2↑↑(n+1) = 2^(2↑↑n)` and
`2↑↑4 = 65536` (upstream `ZInQ.NumericalTowerBounds`). For `T < 2^2^2^9013`,
`(T+1)^2048 < 2^2^2^9014 < 2↑↑7` and `2^((T+1)^2048) < 2↑↑8`, by monotonicity of
exponentiation alone; nothing is evaluated except `2↑↑4`.
-/

namespace ZInQ.Size

open ZInQ.NumericalTowerBounds

theorem tower_zero : hyperoperation 4 2 0 = 1 := NumericalTowerBounds.tower_zero

theorem tower_succ (n : ℕ) : hyperoperation 4 2 (n + 1) = 2 ^ hyperoperation 4 2 n :=
  NumericalTowerBounds.tower_succ n

theorem tower_four : hyperoperation 4 2 4 = 65536 := NumericalTowerBounds.tower_four

/-- The triple power with the power instance of this file (proved with a variable exponent,
so that nothing is evaluated). -/
theorem triplePower_eq_pow (a : ℕ) : triplePower a = 2 ^ 2 ^ 2 ^ a := rfl

theorem quadruplePower_eq_pow (a : ℕ) : quadruplePower a = 2 ^ 2 ^ 2 ^ 2 ^ a := rfl

/-- **Comparison with the towers.** For `T < 2^2^2^9013`:
`(T+1)^2048 < 2^2^2^9014 < 2↑↑7` and `2^((T+1)^2048) < 2↑↑8`. -/
theorem tower_bounds (T : ℕ) (hT : T < 2 ^ 2 ^ 2 ^ 9013) :
    (T + 1) ^ 2048 < 2 ^ 2 ^ 2 ^ 9014 ∧ 2 ^ 2 ^ 2 ^ 9014 < hyperoperation 4 2 7 ∧
      2 ^ (T + 1) ^ 2048 < hyperoperation 4 2 8 := by
  rw [← triplePower_eq_pow] at hT ⊢
  have h1 := degree_bound_of_cutoff_bound T hT
  have h3 := coefficient_bound_of_cutoff_bound T hT
  have hpow : ∀ a b : ℕ, (2 : ℕ) ^ (a + 1) ^ b = 2 ^ (a + 1) ^ b := fun _ _ => rfl
  refine ⟨h1, triplePower_9014_lt_tower_seven, ?_⟩
  exact lt_of_eq_of_lt (hpow T 2048) (h3.trans quadruplePower_9014_lt_tower_eight)

theorem degree_lt_tower_seven (T : ℕ) (hT : T < 2 ^ 2 ^ 2 ^ 9013) :
    (T + 1) ^ 2048 < hyperoperation 4 2 7 :=
  (tower_bounds T hT).1.trans (tower_bounds T hT).2.1

theorem coefficient_lt_tower_eight (T : ℕ) (hT : T < 2 ^ 2 ^ 2 ^ 9013) :
    2 ^ (T + 1) ^ 2048 < hyperoperation 4 2 8 :=
  (tower_bounds T hT).2.2

end ZInQ.Size
