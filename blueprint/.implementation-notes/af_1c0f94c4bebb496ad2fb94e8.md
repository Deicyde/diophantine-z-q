# Implementation note: Size of the program literal

- Lean names: `ZInQ.Compiler.Universal.c3 := code wrapper` (mark `@[irreducible]`; never
  evaluate it), `c3_lt : c3 < 2^(2^24)`, `c3_gt : 1399 < c3`.
- Draft:
  ```lean
  theorem c3_lt : c3 < 2^14400019 := by
    have hw : width wrapper ≤ 18 := width_le_of_fields wrapper_small.2.2
    calc c3 < 2^(width wrapper * (4 * wrapper.length + 1) + 1) := code_lt wrapper
      _ ≤ 2^(18 * (4 * 200000 + 1) + 1) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [wrapper_small.2.1])
  theorem c3_lt' : c3 < 2^(2^24) := c3_lt.trans (Nat.pow_lt_pow_right (by norm_num) (by norm_num))
  theorem c3_gt : 1399 < c3 := ...   -- from code_ge, 3 ≤ wrapper.length, 2 ≤ width
  ```
- Consumers: the size chapter (`|c_3| < 2^(2^24)`, used in its literal-constant bounds; it
  currently quotes the saved literal's 3,181,317 decimal digits, which do not apply to the
  Lean literal) and the shape of the natural precision circuit.
- Mathlib: `Nat.pow_lt_pow_right`, `Nat.pow_le_pow_right`.
- Upstream reuse: none.
- FINITE COMPUTATION: no (the finite part is `wrapper_small`). Difficulty: easy.
