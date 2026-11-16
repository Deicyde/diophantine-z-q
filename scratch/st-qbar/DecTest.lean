import Mathlib

def mulZ {p : ℕ} (n m : Fin 4 → ZMod p) : Fin 4 → ZMod p :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

set_option maxRecDepth 100000 in
theorem d2_3j : ∀ x0 x1 x2 x3 a0 a1 a2 a3 : ZMod 3,
    mulZ ![x0, x1, x2, x3] ![x0, x1, x2, x3] = 0 →
    mulZ (mulZ ![2, 0, 2, 0] ![a0, a1, a2, a3]) ![x0, x1, x2, x3] = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem d1_3j : ∀ x0 x1 x2 x3 : ZMod 3, ![x0, x1, x2, x3] ≠ 0 →
    ∃ b0 b1 b2 b3 : ZMod 3, mulZ ![b0, b1, b2, b3] ![x0, x1, x2, x3] = ![1, 0, 0, 0] ∨
      mulZ ![b0, b1, b2, b3] ![x0, x1, x2, x3] = ![2, 0, 2, 0] := by
  decide +kernel
