# Implementation note: The generator at the two bad primes

- Lean names: `ZInQ.Assembly.val_s_x_genP0`, `ZInQ.Assembly.val_d_x_seven_genP0`.
- FINITE COMPUTATION: yes, two closed statements.
  1. `valPi sqrt2Zs (1641/8 - 145 * s) = -6`: by the model's `ZInQ.val_s_formula`
     (`v_s(a+bs) = min(2v₂a, 2v₂b+1)`) and `padicValRat` of `1641/8`, `-145`: `norm_num`.
  2. `∃ x y h, (7:ℤ) • genP0 = .some x y h ∧ valPi genDZs x = -2`. Method (certificate, kernel
     only, no `native_decide`): an external script computes `[2]P₀, [3]P₀, [6]P₀, [7]P₀` exactly and
     emits their coordinates as rational literals (about 165 digits for `[7]P₀`). In Lean prove
     `2 • P₀ = P₂`, `P₂ + P₀ = P₃`, `2 • P₃ = P₆`, `P₆ + P₀ = P₇` with Mathlib's explicit addition
     (`Point.add_some`, `slope_of_X_ne`/`slope_of_Y_ne`) and `norm_num [QuadraticAlgebra.ext_iff]`
     on the literals; relate `7 • genP0` by `zsmul` unfolding (`7 = 6 + 1`, `6 = 2·3`). Then
     write `x₇ = (α + β s)/γ` with integer literals, `γ > 0`, `gcd(α,β,γ) = 1`, and check by
     `decide`/`norm_num` on `Int` literals that `49 ∣ γ`, `¬ 343 ∣ γ` and `(α + 3β) % 7 ≠ 0`
     (so `d ∤ α + β s`); with `v_d(7) = 1` this gives `v_d(x₇) = 0 - 2 = -2`.
     Size: four group-law steps on numbers below `10^170`; kernel `Nat`/`Int` GMP arithmetic.
  These shapes (`v₇(γ) = 2`, `α + 3β ≡ 2 mod 7`) were confirmed by an exact computation in
  `ℚ(√2)` during blueprint writing.
- Difficulty: easy-medium (~120 lines plus the generated literals).

Shared conventions (assembly notes): namespace `ZInQ.Assembly`, files under
`ZInQKernel/Assembly/`. `RelT τ a` abbreviates `ZInQ.Syntax.Rel τ.poly τ.parameterCount
τ.witnessCount a` (syntax note for template semantics); codes are `ZInQ.iota : ℤ → Fin 5 → ℚ`
and `ZInQ.pointCode` (point-codes note); `genP0 : genCurve.toAffine.Point`. The hypothesis
quadruple `(hH : SixContactEstimate) (hPC : PoleCompleteness) (hMW : MordellWeilE)
(h22 : FixedPrimePattern)` is written `hyps`. The constants `A0`, `Bnk n κ`, `heightD` and
every power `4 ^ Bnk n κ` must stay symbolic: mark them `@[irreducible]`/`noncomputable` and
never use `decide`, `norm_num` evaluation or `#eval` on them.
