# nat-exponential: report

Blueprint section `compiler/natural/exponential/` (16 leaves). Lean modules are under
`ZInQKernel/Compiler/Exponential/`, with root module `ZInQKernel/Compiler/Exponential.lean`
(imported from `ZInQKernel.lean`). All 16 leaves are proved with no `sorry`. `#print axioms`
on every leaf theorem shows only `propext`, `Classical.choice` and `Quot.sound`. No finite
computation was needed. Alpha declarations are in `ZInQ.AlphaPower` (upstream's namespace, as
the implementation notes ask); the bit-level ones are in `ZInQ`.

| Article | Lean name | Status |
| --- | --- | --- |
| `alpha-sequence.md` | `ZInQ.AlphaPower.alphaZ` (upstream), plus new `alphaMat`, `alphaMat_mulVec`, `alphaInt`, `alphaInt_neg`, `alphaInt_add_two` (`AlphaSequence.lean`) | proved |
| `alpha-growth.md` | `alphaZ_growth`, `alphaZ_exponential_bounds` (`AlphaGrowth.lean`) | proved |
| `alpha-matrix.md` | `alphaMat_pow`, `alphaMat_pow_det`, `alphaZ_quadratic`, `alphaZ_quadratic_pred`, `alphaZ_isCoprime_succ`, `alphaZ_not_both_even`, `alphaZ_addition` (`AlphaMatrix.lean`) | proved |
| `alpha-parameter-congruence.md` | `alphaZ_modEq_of_modEq`, `alphaZ_two`, `alphaZ_modEq_index` (`AlphaParameterCongruence.lean`) | proved |
| `alpha-pell.md` | `alphaZ_pell_unordered` (with `alphaZ_pell_index`), `alphaZ_pell_ordered`, `alphaZ_pell_converse` (`AlphaPell.lean`) | proved |
| `alpha-divisibility.md` | `alphaZ_dvd_alphaZ_iff`, `alphaZ_sq_dvd_alphaZ_iff`, `alphaZ_sq_dvd_alphaZ_zero_index` (`AlphaDivisibility.lean`) | proved |
| `alpha-period.md` | `alphaZ_fold_index`, `alphaZ_period`, `alphaZ_reflection`, `alphaZ_folded_residue`, `two_mul_alphaZ_lt_companion'`, `two_mul_alphaZ_lt_companion_self`, `companion_eq`, `companion_eq_trace` (`AlphaPeriod.lean`) | proved |
| `alpha-large-odd.md` | `alphaZ_large_odd` (`AlphaLargeOdd.lean`) | proved |
| `alpha-equations.md` | `ZInQ.AlphaPower.AlphaEqns` (`AlphaEquations.lean`) | proved (definition) |
| `alpha-equations-sound.md` | `alphaEqns_sound` | proved |
| `alpha-equations-complete.md` | `alphaEqns_complete`, `alphaEqns_iff` | proved |
| `power-equations.md` | `ZInQ.AlphaPower.PowEqns` (`PowerEquations.lean`) | proved (definition) |
| `power-equations-correct.md` | `powEqns_iff` | proved |
| `binomial-digit.md` | `ZInQ.binomial_digit_iff_choose` (`BinomialDigit.lean`) | proved |
| `lucas-bits.md` | `ZInQ.lucas_choose_odd_iff_masked`, `ZInQ.lucas_choose_add_odd_iff_disjoint` (`LucasBits.lean`) | proved |
| `bit-and.md` | `ZInQ.bitAnd_gadget_iff` (bitwise form), `ZInQ.bitAnd_macro_iff` (orthogonality-macro form) (`BitAnd.lean`) | proved |

## Statement corrections

No article is wrong. Small differences in form:

- `alpha-period.md`, item 2: `alphaZ_period` and `alphaZ_reflection` drop the hypothesis
  `m > 0`, because the congruences hold for every `m` (upstream proves them this way). This is a
  stronger statement. The reflection is written `v ∣ U_{2lm-j} - (-((-1)^l U_j))`, which is the
  article's congruence `U_{2lm-j} ≡ -(-1)^l U_j`. The "consequently `U_n ≡ ±U_j`" clause is
  `alphaZ_folded_residue`: `v ∣ U_n - U_j ∨ v ∣ U_n + U_j`.
- `alpha-sequence.md`: the article's extension to negative indices is `alphaInt b : ℤ → ℤ`,
  defined as `alphaZ` on `n ≥ 0` and `-alphaZ b (-n)` on `n < 0`. Lean proves it satisfies
  `U_{-n} = -U_n` and the recurrence at every integer index.
- `alpha-growth.md` is split into two theorems. `alphaZ_growth` is the first group of
  inequalities for `b ≥ 2`. `alphaZ_exponential_bounds` holds the two exponential bounds, each
  under its own hypothesis (`1 ≤ c`, `3 ≤ b`).
- `alpha-divisibility.md`, item 2: the divisibility `k U_k ∣ m` is in `ℤ`, as the article
  says. The `k = 0` remark is a separate lemma, `alphaZ_sq_dvd_alphaZ_zero_index`.
- `alpha-equations.md`: each congruence is `p % M = q % M` on naturals, the convention the
  article fixes. `alphaEqns_complete` produces the witness for `X = (alphaZ b N).toNat`.
  `alphaEqns_iff` states the combined equivalence with `(X : ℤ) = alphaZ b N`.
- `binomial-digit.md`: the total is `(β + 1)^N`, in the compiler's order. Upstream's
  `macroHolds` writes `(1 + β)^N`, and the proof bridges the two with `Nat.add_comm`.

## Lemmas added beyond the leaves

- `alphaZ_nonneg`, `alphaZ_strictMono`, `alphaZ_le_of_le`, `alphaZ_lt_of_lt`, `alphaZ_pos`
  (`AlphaGrowth.lean`). These are public monotonicity lemmas; upstream's are private.
- `alphaMat_det`, `alphaInt_natCast`.

## Problems

None. Every leaf reuses upstream's sorry-free helpers (`lean/ZInQ/Alpha*.lean`,
`PowerBoundDraft`, `BinomialDigit`, `BitwiseMacros`). The new proofs are the glue: soundness
(about 60 lines), completeness (about 60 lines), the power formula (about 90 lines), the matrix
power, and the integer-index extension. The build shows "consider adding `module`" warnings
for imports of module-system packages. They are harmless and also appear in other
`ZInQKernel` files.

## Suggestions for the next agent

- The compiler's power template (blueprint `compiler/natural/formulas/`) can use
  `ZInQ.AlphaPower.powEqns_iff` and `alphaEqns_iff` directly. The definitions `PowEqns` and
  `AlphaEqns` list the witnesses in the compiler's order (`b, m, a₀, a₁, a₂` and
  `r, s, t, u, v, w, x, y`). The conditions are written as relations (`<`, `∣`, `%`), not yet as
  equations with gadget witnesses. That translation belongs to the formulas section.
- The bitwise macros (`mask`, `orthogonal`, `bit_and`) are upstream's
  `ZInQ.NaturalBitwiseMacros` definitions. `bitAnd_macro_iff` restates their semantics with
  `&&&`.
