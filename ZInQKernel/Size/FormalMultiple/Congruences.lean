import Mathlib

/-!
# Congruences for `P₀` modulo seven

Blueprint: `size/formal-multiple/bad-place-congruences.md`.

The closed integer statements behind the reduction of `P₀` at the prime `(d)` above `7`:
`8 x(P₀) = 1641 - 1160 s` and `32 y(P₀) = -123720 + 87483 s` reduce under `s ↦ 3` to `8 · 2`
and `32 · 6`, `A = -11243 + 7950 s` reduces to `0`, `6² = 2³`, and `2 · 6`, `3 · 2²`, `8`, `32`
are units modulo `7`. Checked by the kernel (`decide`).
-/

namespace ZInQ.Size

/-- **Congruences for `P₀` modulo seven.** -/
theorem bad_place_congruences :
    (1641 - 1160 * 3 - 2 * 8 : ℤ) % 7 = 0 ∧ (-123720 + 87483 * 3 - 6 * 32 : ℤ) % 7 = 0 ∧
      (-11243 + 7950 * 3 : ℤ) % 7 = 0 ∧ (6 ^ 2 - 2 ^ 3 : ℤ) % 7 = 0 ∧
      (2 * 6 : ℤ) % 7 ≠ 0 ∧ (3 * 2 ^ 2 : ℤ) % 7 ≠ 0 ∧ (8 : ℤ) % 7 ≠ 0 ∧ (32 : ℤ) % 7 ≠ 0 := by
  decide

/-- The same congruences in `𝔽₇`. -/
theorem bad_place_congruences_zmod :
    ((1641 : ℤ) : ZMod 7) + ((-1160 : ℤ) : ZMod 7) * 3 = 8 * 2 ∧
      ((-123720 : ℤ) : ZMod 7) + ((87483 : ℤ) : ZMod 7) * 3 = 32 * 6 ∧
      ((-11243 : ℤ) : ZMod 7) + ((7950 : ℤ) : ZMod 7) * 3 = 0 ∧ (6 : ZMod 7) ^ 2 = 2 ^ 3 ∧
      (2 * 6 : ZMod 7) ≠ 0 ∧ (3 * 2 ^ 2 : ZMod 7) ≠ 0 ∧ (8 : ZMod 7) ≠ 0 ∧ (32 : ZMod 7) ≠ 0 := by
  decide

end ZInQ.Size
