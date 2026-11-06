# Implementation note: The precision constant is the six-contact constant

- Lean name: `ZInQ.Compiler.Precision.A0_eq_heightH6`.
- Draft:
  ```lean
  theorem A0_eq_heightH6 : (A0 : ℝ) = heightH6 (heightD : ℝ)
  theorem heightD_admissible : (10:ℝ)^12 ≤ heightD ∧ ∀ p ≤ 324, (p : ℝ) ≤ heightD
  ```
- Proof: `heightQ D = (D:ℝ) ^ ((D:ℝ) * E0)` is `Real.rpow`; rewrite with
  `Real.rpow_natCast` after `push_cast` (`(D:ℝ) * (E0:ℝ) = ((D*E0 : ℕ) : ℝ)`), then
  `Nat.cast_pow`, `Nat.cast_max`. For `10^12 ≤ D`: `Nat.self_le_factorial`-style bound
  `20! ≤ 324!` (`Nat.factorial_le`) and `decide` on `10^12 < 20!` (small), then `D ≥ F0`
  from `1 ≤ 3^_`.
- Mathlib: `Real.rpow_natCast`, `Nat.factorial_le`, `Nat.one_le_pow`.
- Upstream reuse: hypothesis-file definitions.
- FINITE COMPUTATION: `10^12 < 20!` only (kernel `decide` on 19-digit numbers, trivial).
- Difficulty: easy.
