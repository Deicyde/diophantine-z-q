# bp-record-pp report: recording the progressions chapter

Blueprint-only task: `blueprint/roadmap/progressions/` is now aligned with the Lean in
`ZInQKernel/Progressions/{LSeries,Mertens,RealChar,QuadField,IdealCount}/`. No Lean files were
edited. 28 leaves are recorded (`statement: formalized`, `proof: formalized` for theorems,
`lean:` names), and their implementation notes are deleted. The 4 leaves owned by pp-final are
left unrecorded, with statements and notes aligned to the plan and to the delivered lemma
names. Every recorded `lean:` name (115 in total) was checked by `#check` against the build.
`lake build ZInQKernel`,
`autoform check blueprint --lean-root .` (392 articles, OK) and `autoform audit blueprint`
(OK) all pass. All names are in namespace `ZInQ.Progressions` (prefix omitted below).

## Table

| article | Lean names | status |
| --- | --- | --- |
| lseries/character-sums.md | `norm_sum_char_le`, `norm_sum_Ico_char_le`, `norm_sum_Ioc_char_le`, `sum_Ico_char_period_eq_zero` | proved |
| lseries/tails.md | `norm_sum_mul_antitone_le`, `norm_sum_Ioc_char_div_cpow_le`, `norm_sum_Ioc_char_div_cpow_le_two_mul`, `norm_sum_Ioc_char_log_div_cpow_le`, `norm_sum_Ioc_char_log_div_cpow_le_two_mul`, `norm_LFunction_sub_sum_le`, `norm_tail_le`, `norm_LSeries_logMul_sub_sum_le`, `norm_tail_log_le` | proved |
| lseries/l-value-bound.md | `norm_LFunction_le`, `norm_LFunction_le_of_one_lt`, `norm_LFunction_one_le`, `sum_norm_char_div_cpow_le`, `LFunction_one_le_of_forall_one_lt` | proved |
| lseries/log-partial-sums.md | `norm_partialSum_log_le`, `norm_sum_log_div_le`, `sum_norm_char_log_div_cpow_le`, `mul_log_succ_rpow_neg_le` | proved |
| lseries/derivative-bound.md | `norm_deriv_LFunction_le`, `deriv_LFunction_eq` | proved |
| lseries/l-value-variation.md | `norm_LFunction_sub_one_le`, `continuous_LFunction_ofReal` | proved |
| lseries/partial-sums.md | `norm_sum_div_sub_LFunction_one_le`, `norm_partialSum_sub_LFunction_one_le`, `norm_partialSum_sub_LFunction_one_le'`, `continuous_sum_char_div_cpow` | proved |
| lseries/trivial-character.md | `norm_LSeries_one_le`, `tsum_one_div_succ_rpow_le_one_add_inv` | proved |
| lseries/complex-lower-bound.md | `norm_LFunction_one_ge_of_sq_ne_one` | proved |
| quadratic-fields/quadratic-field.md (def) | `Qsqrt`, `Qsqrt.instNumberField`, `Qsqrt.instCharZero`, `Qsqrt.finrank`, `Qsqrt.not_isSquare_of_squarefree`, `Qsqrt.fact_not_isSquare`, `Qsqrt.sqrtInt`, `Qsqrt.sqrtInt_sq` | statement formalized (definition) |
| quadratic-fields/discriminant-bound.md | `Qsqrt.abs_discr_le`, `Qsqrt.exists_four_mul_eq_sq_mul_discr`, `Qsqrt.discr_basis` | proved |
| quadratic-fields/signature.md | `Qsqrt.nrRealPlaces_of_neg`, `Qsqrt.nrComplexPlaces_of_neg`, `Qsqrt.nrRealPlaces_of_pos`, `Qsqrt.nrComplexPlaces_of_pos`, `Qsqrt.isTotallyReal`, `Qsqrt.isTotallyComplex` | proved |
| quadratic-fields/roots-of-unity.md | `Qsqrt.torsionOrder_le_six`, `torsionOrder_le_six_of_finrank_eq_two`, `le_six_of_totient_le_two` | proved |
| quadratic-fields/imaginary-regulator.md | `Qsqrt.regulator_of_neg` | proved |
| quadratic-fields/real-regulator.md | `Qsqrt.regulator_ge_of_pos`, `Qsqrt.unit_quadratic`, `golden_le_of_quadratic`, `log_golden_le_abs_log` | proved |
| quadratic-fields/residue-bound.md | `dedekindZeta_residue_ge`, `log_golden_pos`, `log_golden_lt_one` | proved |
| ideal-counts/ideal-count.md (def) | `idealCount`, `dedekindZeta_eq_LSeries_idealCount`, `IdealCount.LSeriesSummable_idealCount` | statement formalized (definition) |
| ideal-counts/multiplicative.md | `idealCount_mul`, `idealCount_one`, `idealCountMulEquiv` | proved |
| ideal-counts/local-factors.md | `localEps`, `localEps_mem`, `idealCount_prime_pow`, `exists_localFactor`, `eq_localEps_of_idealCount_prime_pow`, `idealCount_prime_pow_cases`, `IdealCount.tsum_term_idealCount_prime_pow`, `IdealCount.norm_localEps_le_one` | proved |
| ideal-counts/splitting-law.md | `localEps_eq_legendreSym`, `idealCount_prime_eq_legendreSym`, `idealCount_prime_pow_eq_legendreSym`, `IdealCount.idealCount_prime_eq_card_ringHom`, `IdealCount.card_ringHom_eq_card_sqrt` | proved |
| ideal-counts/zeta-factorization.md | `dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod`, `dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod_of_legendreSym`, `dedekindZeta_eq_mul_prod_of_localEps_eq`, `IdealCount.hasProd_dedekindZeta` | proved |
| real-characters/classification.md | `exists_legendre_of_real_char`, `exists_legendre_of_real_char_dvd` | proved |
| counting/mertens.md | `mertensSum`, `abs_mertensSum_sub_log_le`, `log_sub_two_le_mertensSum`, `mertensSum_le_log_add_three`, `psi_le_three_mul`, `psi_div_le_three` | proved |
| counting/prime-powers.md | `sum_nonprime_vonMangoldt_div_le_two`, `sum_Ioc_nonprime_vonMangoldt_div_le`, `sum_vonMangoldt_mul_le_sum_primePow`, `sum_Icc_log_div_mul_pred_le'` | proved |
| counting/orthogonality.md | `classSum`, `twistedSum`, `classSum_eq_sum_twistedSum`, `classSum_sub_eq`, `dirichletCharacter_apply_inv_of_isUnit` | proved |
| counting/principal-character.md | `log_div_sub_le_re_twistedSum_one_sub`, `twistedSum_one_eq`, `sum_nonunit_vonMangoldt_div_le_log` | proved |
| counting/twisted-sum-bound.md | `norm_LFunction_one_mul_norm_twistedSum_le_explicit`, `norm_twistedSum_le`, `norm_LFunction_one_mul_norm_twistedSum_le`, `norm_LFunction_one_mul_norm_twistedSum_le_of`, `logSum_eq_sum`, `logSum`, `recipSum` | proved |
| counting/twentytwo-primes.md | `twentytwo_primes_of_twisted_bound`, `twentytwo_primes_of_LFunction_lower_bound`, `classSum_sub_ge`, `sum_Ioc_classSum_le` | proved |
| real-characters/real-lower-bound.md | proposed `norm_LFunction_one_ge_of_sq_eq_one` (pp-final) | not done |
| counting/uniform-lower-bound.md (was uniform-twisted-bound.md) | proposed `norm_LFunction_one_ge_min` (pp-final) | not done |
| effective-dirichlet.md | proposed `effective_dirichlet` (pp-final) | not done |
| catalogue-instance.md | proposed `catalogueBound8`, proving `ZInQ.CatalogueBound8` (pp-final) | not done |

## Statement corrections (article prose changed to match the Lean)

- **Ranges in σ (lseries).** `l-value-bound`: `|L(σ,χ)| ≤ M` for every real `σ ≥ 1` (was
  `1 ≤ σ ≤ 2`). `l-value-variation`: every `σ ≥ 1`. `derivative-bound`: only for `σ > 1`, with
  no upper bound, and the formula `L'(σ,χ) = −Σ χ(n) log n n^{-σ}` is added. The title is now
  "… to the right of 1". The Lean has no bound at `σ = 1`, and the variation bound needs none.
  The proof is now a direct split at `N = q` and depends on `tails`, not on
  `log-partial-sums`.
- **log-partial-sums** is stated at `σ = 1` only (every real `x`). The Lean has no
  `σ ≥ 1` version of the partial-sum bound; the derivative bound does not need one.
- **tails**: the sharp forms `q(N+1)^{-σ}` (for `σ ≥ 0`, any `N`) and `q log(N+1)(N+1)^{-σ}`
  (for `N ≥ 2`) are added, along with the infinite tails for `σ > 1`. The `2q/N` and
  `2q log N/N` forms keep `N ≥ 1` and `N ≥ 3` respectively.
- **partial-sums**: adds the sharper `q/(N+1)` for every integer `N ≥ 0`, and `2q/x` now holds
  for every real `x > 0` (was `x ≥ 1`).
- **character-sums**: both the `[a, b)` and `(a, b]` forms, for all `a, b ≥ 0`, plus the zero
  sum over a period.
- **trivial-character**: holds for every modulus and is stated for the Dirichlet series.
- **Quadratic fields.** The hypothesis "d squarefree, d ≠ 1" is replaced throughout by "d is
  not the square of a rational number", which is weaker. Squarefree `d ≠ 1` qualifies, and the
  `quadratic-field` article says so. `quadratic-field` also records the integral `√d`.
  `imaginary-regulator` now states only `R_K = 1`, for every integer `d < 0`; the rank-0 claim
  moved into the proof. `real-regulator` holds for every non-square `d > 0` (was `d > 1`
  squarefree). `roots-of-unity` holds for every number field of degree 2. `discriminant-bound`:
  the proof sketch now follows the Lean route through an integral basis; the ring of integers
  is never computed.
- **Ideal counts.** `ideal-count`: `a_K(n)` is defined for every `n ≥ 0`. `multiplicative`:
  for coprime natural numbers, and the proof follows the Lean route (`I ↦ (I+(m), I+(n))`,
  with no prime factorization). `local-factors`: adds uniqueness of `ε_p`, and states the
  Euler factor for complex `s` with `Re s > 0` (was real `s > 0`). `splitting-law` is now
  stated for any degree-2 field `K` with `α ∈ O_K`, `α² = d`, and **`d` not a square**. The
  article gives the counterexample `Q(i)`, `α = 1`, `d = 1`, `p = 3`. It also adds
  `a_K(p) = 1 + (d/p)` and the prime-power formula, and the proof is the Lean one (ring
  homomorphisms to `Z/p`, a trace identity; no Kummer–Dedekind). `zeta-factorization`: the
  main form assumes only `ε_p = χ(p)` for primes `p ∤ 2q`, for any degree-2 field. The
  Legendre-symbol situation is stated as a sufficient condition, with "no prime `p ∤ 2q`
  divides `d`" in place of "every prime factor of `d` divides `2q`". The general version for
  any finite set `P` of primes (complex `s`, `Re s > 1`) is added. `q ≥ 1` is necessary.
- **classification**: `|d|` divides `q`, and `8 | q` if `d` is even (stronger than the old
  `|d| ≤ q`, "every prime factor divides 2q"). The proof sketch follows the Lean route
  (Hensel lifting, a real character is 1 on unit squares, induction over coprime factors).
- **Counting.** `mertens`: the constant is **3**, with `log x − 2 ≤ Σ ≤ log x + 3` (was 6),
  plus Chebyshev's `ψ(x) ≤ 3x`. `prime-powers`: the constant is **2**, for integer `N` (was
  3, real `x`), plus the tail bound
  `Σ_{Y<n≤M, n not prime} Λ(n)/n ≤ (log s + 2 + 2 log 4)/s`, `s = ⌊√Y⌋`. `orthogonality` is
  stated for `f = Λ(n)/n` on `n ≤ x` only (the Lean has no general `f`, `S` form), with the
  character weight `χ(a⁻¹)`, plus the real-part form for differences. `principal-character`:
  the constant is **6** (was 12), plus `Σ_{n≤N, gcd(n,q)>1} Λ(n)/n ≤ log q`.
  `twisted-sum-bound`: `M² + 6q` (was `M² + 12q`), together with the intermediate
  `|T(x)| + 2qψ(x)/x` and the quotient form `|S_χ(x)| ≤ (M² + 6q)/|L(1,χ)|`.
  `twentytwo-primes` is rewritten to the delivered statement: `q ≥ 3`, `B ≥ 1`, primes in
  `(q^8, q^8 e^{5qB}]` (was `q ≥ 1`, `B ≥ 0`, any `(y, x]` with
  `log(x/y) ≥ q(2B+11)+12+log q`). It adds the corollary from a lower bound `c` on all
  `|L(1,χ)|`, with `B = ((log q+3)² + 6q)/c`.

## pp-final leaves (aligned, not recorded)

- `real-lower-bound`: the statement is unchanged (`|L(1,χ)| ≥ 1/(40 q^{3/2})`). The proof
  sketch and the note now use the delivered inputs: `exists_legendre_of_real_char_dvd`,
  `Qsqrt`, `Qsqrt.sqrtInt(_sq)`, `Qsqrt.finrank`, `Qsqrt.not_isSquare_of_squarefree`,
  `dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod_of_legendreSym`,
  `IdealCount.norm_localEps_le_one`, `IdealCount.norm_natCast_cpow_neg_lt_one`, and
  `dedekindZeta_residue_ge`.
- `counting/uniform-twisted-bound.md` is **renamed** to `counting/uniform-lower-bound.md`,
  keeping the same article_id. It now states the bound for all characters as
  `|L(1,χ)| ≥ min(1/(256M⁷), 1/(40q^{3/2}))` for every `χ ≠ χ₀`. The reason:
  `twentytwo_primes_of_LFunction_lower_bound` consumes exactly such a `c`, and the
  `2^24 q^5` twisted-sum bound is no longer needed. The name `norm_twistedSum_le`, which the
  old note proposed, is taken by the quotient form. Proposed name: `norm_LFunction_one_ge_min`.
- `effective-dirichlet`: the statement is unchanged (`q ≥ 2^16`, `q² < p < 2^{q^8}`, as in
  the plan). The proof now runs through `uniform-lower-bound` and
  `twentytwo_primes_of_LFunction_lower_bound`: `1/c ≤ 2^20 q^{7/2}`,
  `8 log q + 5qB ≤ 2^28 q^{11/2} < 2^39 q^{11/2} ≤ q^8 log 2`. The note says that the stronger
  lower end `q^8` comes for free.
- `catalogue-instance`: the statement matches `ZInQ.CatalogueBound8`. The note names
  `ZInQ.Size.W_gt` and `ZInQ.Syntax.W_eq_catalogueModulus`.

## Lemmas added beyond the leaves

None (no Lean edits).

## Problems

None blocking.

## Suggestions for the next agent

- `blueprint/roadmap/main/catalogue-bound.md`, outside this chapter, states the `2^{W^8}`
  cutoff but its `lean:` field is `ZInQ.CatalogueBound`, which is the `2^{W^3}` version. It
  should probably be `ZInQ.CatalogueBound8`.
- pp-final: if `effective_dirichlet` is proved with the lower end `q^8`, update the article's
  interval to `(q^8, 2^{q^8})` when recording it. If the real-character bound uses
  `q * √q`, spell `uniform-lower-bound` the same way.
