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

## From the deleted duplicates `assembly/approximation/precision-predicate.md` and `precision-acceptance.md`

- Upstream reuse: `ZInQ.HeightConstantAlgorithm.heightConstant` (`lean/ZInQ/HeightConstantAlgorithm.lean`)
  is literally `2·10^13·max (max 1 cCm) (q0^17)` with `r = max (max d 317) (10^12)`, and
  `ZInQ.HeightConstantComparison.h6_for_max_317_eq_height_constant` identifies it with the
  parameterized `H6`. Bridge to `ZInQ.heightH6` (`ZInQKernel/Hypotheses/Height.lean`, real
  `rpow`) with `Real.rpow_natCast`, `Nat.cast_max`.
- `10^12 ≤ D` without evaluating `D`: `D = F0 * 3^_ ≥ F0` (`Nat.le_mul_of_pos_right`,
  `pow_pos`), `F0 = 324! ≥ 15!` (`Nat.factorial_le`) and `10^12 < 15!` by `decide` or `norm_num`
  on a 13-digit number; then `max (max D 317) (10^12) = D` by `max_eq_left`. Never unfold `D`
  or `324!` further.
