# pp-mertens report: plan step 4 (Mertens' theorem and the residue-class count)

All modules are in `ZInQKernel/Progressions/Mertens/`, namespace `ZInQ.Progressions`, root
`ZInQKernel/Progressions/Mertens.lean` (imported from `ZInQKernel.lean`). They import Mathlib and
`ZInQKernel.Progressions.LSeries.PartialSum` (merged from `origin/wip/pp-lseries`) only. There is
no `sorry`, no axiom and no `native_decide`. `lake build ZInQKernel` succeeds.

There are no blueprint leaves for this phase yet, so the table lists the plan items.

| Plan item | Lean name (module) | Status |
| --- | --- | --- |
| 4.1 Mertens' first theorem, `\|Σ_{n≤x} Λ(n)/n − log x\| ≤ C₀` with `C₀ = 3` (x ≥ 1) | `abs_mertensSum_sub_log_le` (First) | proved |
| 4.1 one-sided forms, `log x − 2 ≤ S(x) ≤ log x + 3` | `log_sub_two_le_mertensSum`, `mertensSum_le_log_add_three` (First) | proved |
| 4.1 Chebyshev, `ψ(x) ≤ 3x` (x ≥ 0) and `ψ(x)/x ≤ 3` | `psi_le_three_mul`, `psi_div_le_three` (First) | proved |
| 4.3 orthogonality, `S_a(x) = φ(q)⁻¹ Σ_χ χ(a⁻¹) S_χ(x)` | `classSum_eq_sum_twistedSum` (Orthogonality) | proved |
| 4.3 orthogonality for differences (real part) | `classSum_sub_eq` (Orthogonality) | proved |
| 4.2 conditional, `‖L(1,χ)‖‖S_χ(x)‖ ≤ ‖T(x)‖ + 2qψ(x)/x` given the partial-sum estimate | `norm_LFunction_one_mul_norm_twistedSum_le_of` (Twisted) | proved |
| 4.2 unconditional (χ ≠ 1, x ≥ 1) | `norm_LFunction_one_mul_norm_twistedSum_le` (Unconditional) | proved |
| 4.2 explicit, `‖L(1,χ)‖‖S_χ(x)‖ ≤ M² + 6q`, `M = log q + 3` | `norm_LFunction_one_mul_norm_twistedSum_le_explicit`, `norm_twistedSum_le` (Unconditional) | proved |
| 4.3 principal character, `S_{χ₀}(x) − S_{χ₀}(y) ≥ log(x/y) − 2·3 − log q` for 1 ≤ y ≤ x | `log_div_sub_le_re_twistedSum_one_sub` (Principal) | proved |
| 4.4 prime powers `p^k`, k ≥ 2, `p^k > Y` contribute ≤ `E(Y) = (log s + 2 + 2 log 4)/s`, `s = ⌊√Y⌋` | `sum_Ioc_nonprime_vonMangoldt_div_le` (PrimePowers) | proved |
| 4.4 each prime p > y contributes ≤ log y / y (y ≥ 3) | `log_div_self_le_of_three_le` (Count) | proved |
| 4.4 class sum over `(Y, M]` ≤ #primes · log Y/Y + E(Y) | `sum_Ioc_classSum_le` (Count) | proved |
| 4.4 lower bound for `S_a(x) − S_a(y)` from ‖S_χ‖ ≤ B | `classSum_sub_ge` (Count) | proved |
| 4.4 **22 primes** p ≡ a (mod q) with `q^8 < p ≤ q^8·exp(5qB)` | `twentytwo_primes_of_twisted_bound` (Count) | proved |
| 4.4 22 primes from `c ≤ ‖L(1,χ)‖` for all χ ≠ 1, with `B = ((log q + 3)² + 6q)/c` | `twentytwo_primes_of_LFunction_lower_bound` (Unconditional) | proved |

## Definitions (Defs, First)

All sums run over `n ∈ Finset.Ioc 0 ⌊x⌋₊`, as in `Chebyshev.psi` and in pp-lseries's
`PartialSum.lean`:

- `mertensSum x = Σ Λ(n)/n` (real);
- `twistedSum χ x = S_χ(x) = Σ χ(n)Λ(n)/n` (complex);
- `classSum a x = S_a(x) = Σ_{n ≡ a} Λ(n)/n` for `a : ZMod q` (real);
- `recipSum χ y = Σ χ(m)/m`;
- `logSum χ x = T(x) = Σ χ(n) log n / n`.

`recipSum` and `logSum` unfold to exactly the sums in pp-lseries's
`norm_partialSum_sub_LFunction_one_le` and `norm_partialSum_log_le`. Those lemmas apply to them
as they stand.

## Statement notes and changes from the plan

- **C₀ = 3.** The plan says "2 is classical". The proof gives `−2 ≤ S(x) − log x ≤ 3`. The upper
  side is `ψ(N)/N ≤ 3`, from Mathlib's `Chebyshev.psi_le` together with `log x ≤ 2√x/e`.
  Mathlib's own `psi_le_const_mul_self` only gives `log 4 + 4 ≈ 5.39`. Item 4 is therefore
  stated with `2·3`.
- **Orthogonality** is stated with `χ a⁻¹` (`χ` applied to `a⁻¹ ∈ ZMod q`), following Mathlib's
  `sum_char_inv_mul_char_eq`. `dirichletCharacter_apply_inv_of_isUnit` gives `χ a⁻¹ = (χ a)⁻¹`
  for a unit `a`.
- **Principal character.** The plan's step 4.3 has `− 2 log q`; one `log q` suffices. The
  integers not coprime to `q` contribute at most `Σ_{p|q} log p/(p−1) ≤ log q`
  (`sum_nonunit_vonMangoldt_div_le_log`).
- **E(y).** The plan says "about 4 log y/√y". The proved bound is
  `E(Y) = (log ⌊√Y⌋ + 2 + 2 log 4)/⌊√Y⌋`, about `(½ log Y + 4.8)/√Y`, which is smaller. Primes
  `p ≤ √Y` give at most `2θ(√Y)/Y`, and primes `p > √Y` give at most
  `Σ_{n>s} log n/(n(n−1)) ≤ (log s + 2)/s` by telescoping. A cruder bound that does not depend on
  `Y` is also proved: the non-primes contribute at most 2 in total
  (`sum_nonprime_vonMangoldt_div_le_two`).
- **The count** has the plan's constant: `q^8 < p ≤ q^8·exp(5qB)`. Hypotheses: `3 ≤ q`,
  `a : ℕ` with `a.Coprime q`, `1 ≤ B`, and `‖twistedSum χ x‖ ≤ B` for every `χ ≠ 1` and every
  real `x ≥ 1`. Conclusion:
  `22 ≤ #{p ∈ Ioc (q^8) ⌊(q:ℝ)^8 * exp (5*q*B)⌋₊ | p.Prime ∧ p ≡ a [MOD q]}`. The proof
  gives `S_a(x) − S_a(q^8) ≥ 1`. On the other side, 21 primes contribute at most
  `21·16/6561` and the prime powers at most `16/81`.
- **Typeclasses.** Statements that mention `DirichletCharacter.LFunction` take `[NeZero q]`,
  because Mathlib's `LFunction` needs it. `twentytwo_primes_of_twisted_bound` does not.

## Lemmas added beyond the plan items

`sum_vonMangoldt_mul_le_sum_primePow`: a sum of `Λ(n)h(n)` is at most the double sum over the
primes `p` and exponents `k` that cover its prime powers. Also `sum_Icc_log_div_mul_pred_le`
(the telescoping bound), `sum_Ico_one_div_pow_le_of_two_le`, `logSum_eq_sum` (the identity
`T(x) = Σ_d χ(d)Λ(d)/d · Σ_{m≤x/d} χ(m)/m`), `twistedSum_one_eq`,
`mul_mertensSum_bounds`, `sum_log_eq_sum_vonMangoldt_mul_div`,
`classSum_sub_classSum_nat`.

## Problems

None open. No finite-computation hypotheses were needed: every numeric check is a short
`norm_num`/`linarith` step, using `log 3 ≤ 2`, `log 4 ≤ 3` and Mathlib's `exp_one_gt_d9` and
`log_two_lt_d9`.

## Suggestions for the next agent (assembly at q = W)

- Use `twentytwo_primes_of_LFunction_lower_bound`. It needs only `3 ≤ q`, `a.Coprime q`, and a
  uniform `c > 0` with `c ≤ ‖L(1,χ)‖` for all `χ ≠ 1`. Take `c` as the minimum of the
  complex-character bound (pp-lseries, step 2: `1/(256 M⁷)`) and the real-character bound
  (step 3: about `q^{-3/2}/40`).
- The prime bound is then `q^8·exp(5q((log q+3)² + 6q)/c)`. For `q = W` this has to be shown
  `< 2^(W^8)`. Roughly: `5q(M² + 6q)/c ≤ 5q·7q·256·M⁷` in the complex case, and about
  `5q·7q·40 q^{3/2}` in the real case, both far below `W^8 log 2`. Reason symbolically and never
  evaluate `W`.
- The lower end `q^8 = W^8 > 324` covers the `(324, ·)` side of `CatalogueBound8`.
