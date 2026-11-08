# pp-lseries report: plan steps 1 and 2 (explicit L-function bounds near s = 1)

Spec: `docs/effective-dirichlet-plan.md`, steps 1 and 2. All Lean code is in
`ZInQKernel/Progressions/LSeries/` (root module `ZInQKernel/Progressions/LSeries.lean`, imported
from `ZInQKernel.lean`), namespace `ZInQ.Progressions`. It imports Mathlib only. Everything is
proved: no `sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound` (checked with
`#print axioms`), and no finite-computation hypotheses. `lake build ZInQKernel` succeeds.

Setting throughout: `{q : ℕ} [NeZero q]`, `χ : DirichletCharacter ℂ q`, `hχ : χ ≠ 1`,
`M = Real.log q + 3`, `L = DirichletCharacter.LFunction χ`. Sums `Σ_{n≤x}` are spelled
`∑ n ∈ Finset.Ioc 0 ⌊x⌋₊`, the same convention as `Chebyshev.psi`. Terms are spelled
`χ n / (n : ℂ) ^ (σ : ℂ)`, `χ n * (Real.log n : ℂ) / (n : ℂ) ^ (σ : ℂ)`, and at `s = 1`
`χ n / (n : ℂ)` and `χ n * (Real.log n : ℂ) / (n : ℂ)`.

## Deliverables

| plan item | Lean name (file) | statement | status |
| --- | --- | --- | --- |
| 1. character sums | `norm_sum_char_le` (CharSum) | `‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n‖ ≤ q` for every real `x` | proved |
| 1. (interval form) | `norm_sum_Ico_char_le`, `norm_sum_Ioc_char_le` (CharSum) | `‖∑ n ∈ Ico a b, χ n‖ ≤ q`, same for `Ioc a b` | proved |
| 2. finite tail | `norm_sum_Ioc_char_div_cpow_le` (Tail) | `0 ≤ σ`: `‖∑_{Ioc N K} χ n/n^σ‖ ≤ q (N+1)^(-σ)` | proved |
| 2. finite tail, plan form | `norm_sum_Ioc_char_div_cpow_le_two_mul` (Tail) | `1 ≤ σ`, `1 ≤ N`: `≤ 2q/N` | proved |
| 2. finite log tail | `norm_sum_Ioc_char_log_div_cpow_le` (Tail) | `1 ≤ σ`, `2 ≤ N`: `‖∑_{Ioc N K} χ n log n/n^σ‖ ≤ q log(N+1) (N+1)^(-σ)` | proved |
| 2. finite log tail, plan form | `norm_sum_Ioc_char_log_div_cpow_le_two_mul` (Tail) | `1 ≤ σ`, `3 ≤ N`: `≤ 2q log N/N` | proved |
| 2. infinite tail (σ > 1) | `norm_LFunction_sub_sum_le` (Tail) | `‖L σ − ∑_{Ioc 0 N} χ n/n^σ‖ ≤ q (N+1)^(-σ)` | proved |
| 2. infinite tail, plan form | `norm_tail_le` (Tail) | `1 < σ`, `1 ≤ N`: `≤ 2q/N` | proved |
| 2. infinite log tail (σ > 1) | `norm_LSeries_logMul_sub_sum_le` (Tail) | `2 ≤ N`: `‖LSeries (logMul ↗χ) σ − ∑_{Ioc 0 N} χ n log n/n^σ‖ ≤ q log(N+1)(N+1)^(-σ)` | proved |
| 2. infinite log tail, plan form | `norm_tail_log_le` (Tail) | `1 < σ`, `3 ≤ N`: `≤ 2q log N/N` | proved |
| 3. `‖L σ‖ ≤ M` | `norm_LFunction_le` (Bounds) | `1 ≤ σ → ‖L σ‖ ≤ log q + 3` | proved |
| 3. `‖L' σ‖ ≤ M²` | `norm_deriv_LFunction_le` (Bounds) | `1 < σ → ‖deriv L σ‖ ≤ (log q + 3)^2` | proved |
| 3. mean value | `norm_LFunction_sub_one_le` (Bounds) | `1 ≤ σ → ‖L σ − L 1‖ ≤ (σ − 1)(log q + 3)^2` | proved |
| 3. `‖L 1‖ ≤ M` | `norm_LFunction_one_le` (Bounds) | `‖L 1‖ ≤ log q + 3` | proved |
| 4. partial sums at 1 | `norm_partialSum_sub_LFunction_one_le` (PartialSum) | `1 ≤ x`: `‖∑_{Ioc 0 ⌊x⌋₊} χ n/n − L 1‖ ≤ 2q/x` | proved |
| 4. (sharper / all x > 0) | `norm_sum_div_sub_LFunction_one_le`, `norm_partialSum_sub_LFunction_one_le'` (PartialSum) | `≤ q/(N+1)` for the sum up to `N`; `≤ 2q/x` for every `x > 0` | proved |
| 4. log partial sums | `norm_partialSum_log_le` (PartialSum) | `‖∑_{Ioc 0 ⌊x⌋₊} χ n log n/n‖ ≤ (log q + 3)^2` for every real `x` | proved |
| 5. complex characters | `norm_LFunction_one_ge_of_sq_ne_one` (ComplexChar) | `χ^2 ≠ 1 → 1/(256 (log q + 3)^7) ≤ ‖L 1‖` | proved |

## Statement corrections and constant changes

None of the constants got worse; some are better or have wider ranges:
- Item 3 holds for every `σ > 1` (resp. `σ ≥ 1`), not only for `σ ∈ (1, 2]`, so the
  statements have no upper bound on `σ`. `norm_LFunction_le` includes `σ = 1`.
- Tails: summation by parts gives `q (N+1)^(-σ)` and `q log(N+1) (N+1)^(-σ)`, i.e. `q/N` and
  `q log N / N`. The plan's `2q/N` and `2q log N/N` are delivered as corollaries (`*_two_mul`,
  `norm_tail_le`, `norm_tail_log_le`). The non-log tail needs only `N ≥ 1`. The log tail needs
  `N ≥ 2` in the sharp form (`log t/t^σ` decreases from `t = 3`) and `N ≥ 3` in the plan form.
- Item 4: the proof gives `q/(⌊x⌋+1) ≤ q/x`, delivered as `2q/x` as planned. It holds for every
  `x > 0` (the primed lemma: for `x < 1` the sum is empty and `‖L 1‖ ≤ M ≤ 2q`).
- Item 4 (log): the bound `M²` holds for every real `x` (for `x < 1` the sum is empty). It is a
  statement about finite sums only, proved by summation by parts. No limit is involved.
- Item 2 at `σ = 1`: no conditional series is used. `L 1` is reached by continuity of
  `L` at 1 (`LFunction` is entire for `χ ≠ 1`) from the absolutely convergent series at
  `σ > 1`, with the uniform tail bound (`norm_sum_div_sub_LFunction_one_le`).
- Item 5: the hypothesis is `χ ^ 2 ≠ 1` only (it implies `χ ≠ 1` and in fact `q ≥ 3`, but the
  statement does not need `q ≥ 3`). The proof uses `x = 1/(256 M⁹)`, as in the plan.
- Infinite log tails are stated for `LSeries (LSeries.logMul ↗χ) σ`, which is
  `−deriv L σ` for `σ > 1` (`deriv_LFunction_eq`).

## Lemmas added beyond the deliverables (all in `ZInQ.Progressions`)

- CharSum: `sum_Ico_char_period_eq` (`q` consecutive values of `χ` run through `ZMod q`),
  `sum_Ico_char_period_eq_zero`, `norm_sum_mul_antitone_le` (summation by parts against a
  nonnegative nonincreasing real weight: `‖∑_{N<n≤K} c n f n‖ ≤ B f(N+1)` if all partial sums
  `‖∑_{N<n≤m} c n‖ ≤ B`; reusable, e.g. by pp-mertens).
- Tail: `norm_hasSum_sub_sum_Ioc_le_of_forall` (uniform finite-tail bounds bound the infinite
  tail), `char_div_cpow_eq`, `char_log_div_cpow_eq`, `log_mul_rpow_neg_succ_le`,
  `natSucc_rpow_neg_le_inv`, `log_natSucc_div_le_log_div`, `abscissaOfAbsConv_char_le_one`,
  `term_logMul_char_eq`.
- Bounds: `two_le_modulus_of_char_ne_one`, `sum_Ioc_natCast_inv_le_one_add_log`,
  `sum_norm_char_div_cpow_le` (head `≤ 1 + log N`), `sum_norm_char_log_div_cpow_le`
  (head `≤ log N (1 + log N)`), `norm_LFunction_le_of_one_lt`, `continuous_LFunction_ofReal`,
  `LFunction_one_le_of_forall_one_lt`, `deriv_LFunction_eq` (`deriv L σ = −LSeries (logMul ↗χ) σ`
  for `σ > 1`), `mul_log_succ_rpow_neg_le`.
- PartialSum: `continuous_sum_char_div_cpow`, `norm_sum_log_div_le` (the `ℕ`-indexed form of
  the log bound).
- ComplexChar: `tsum_one_div_succ_rpow_le_one_add_inv` (`∑_{n≥1} n^(-(1+x)) ≤ 1 + 1/x`, from
  Mathlib's `ZetaAsymptotics.zeta_limit_aux1`), `norm_LSeries_one_le`
  (`‖L(1+x, χ₀)‖ ≤ 1 + 1/x` for the trivial character, `LSeries` form, no `NeZero`).

## Problems

None open. The proofs are short (each module builds in about 5 s). No finite computation is
involved.

## Suggestions for the next agent

- pp-mertens (step 4.2) can apply `norm_partialSum_sub_LFunction_one_le'` to `R(y)` for every
  `y > 0`, and `norm_sum_log_div_le` to `T(x)`. The constants are `q/(⌊y⌋+1)` and `M²`.
- pp-final: combine `norm_LFunction_one_ge_of_sq_ne_one` (complex `χ`) with the step 3 bound
  `L(1,χ) ≥ c q^(-3/2)` (real `χ`). For large `q` the real-character bound is the smaller one.
- To reuse the summation-by-parts lemma for other weights, supply `hf0`/`hf` (nonnegative and
  nonincreasing from `N + 1` on) and the partial-sum bound `hB`.
