# Implementation note: The precision relation

- Lean name: `ZInQ.Compiler.Precision.accepts (c : Fin 5 → ℕ) : Prop`.
- Draft:
  ```lean
  def contacts : Finset ℤ := {0, -15, -20, -24, -30, -60}
  def accepts (c : Fin 5 → ℕ) : Prop :=
    let n := dec (c 0); let κ := dec (c 1); let a := dec (c 2); let l := dec (c 3); let j := dec (c 4)
    n ∉ contacts ∧ κ ≠ 0 ∧ 1 ≤ a ∧ 1 ≤ l ∧ j = n * a ∧
    Admissible l ∧ Admissible a ∧ Admissible j ∧
    |rRatio a j - n| < epsIdx l ∧ 4 * epsIdx l * 4 ^ bound n κ < 1
  ```
  Keep it a `Prop` (not `Bool`); `decide` is never applied to it. The assembly chapter
  consumes it (precision contract of Section 11): agree on the name.
- Mathlib: `Finset` membership, `ℚ` order.
- Upstream reuse: none (the hypothesis file's `contactSet` is a `Finset ℚ`; use
  `(n : ℚ) ∉ contactSet` if the assembly chapter prefers).
- FINITE COMPUTATION: no. Difficulty: trivial.
