# bp-progressions: blueprint for removing CAT

New chapter `blueprint/roadmap/progressions/` (32 leaves, 6 containers), sources file
`blueprint/sources/progressions-locators.md`, 32 implementation notes under
`blueprint/.implementation-notes/`, and the size and main articles restated for the cutoff
`2^(W^8)`. No Lean file was edited. `autoform check blueprint` and `autoform audit blueprint`
both pass with no warnings (392 articles, 1256 dependencies; 22 ready to state, 10 planned).

## Leaves

Status is the Lean status; every leaf is a new article without `lean:`/`statement:` fields.
All names are in namespace `ZInQ.Progressions`; names marked (proposed) are not in the plan's
list.

| Article path | Lean name | Status |
| --- | --- | --- |
| progressions/lseries/character-sums.md | `norm_sum_char_le` | proved on `wip/pp-lseries` (not recorded) |
| progressions/lseries/tails.md | `norm_tail_le` | halves proved on `wip/pp-lseries` as `norm_sum_Ioc_char_div_cpow_le_two_mul`, `norm_sum_Ioc_char_log_div_cpow_le_two_mul` |
| progressions/lseries/l-value-bound.md | `norm_LFunction_le` | not done |
| progressions/lseries/log-partial-sums.md | `norm_partialSum_log_le` | not done |
| progressions/lseries/derivative-bound.md | `norm_deriv_LFunction_le` | not done |
| progressions/lseries/l-value-variation.md | `norm_LFunction_sub_one_le` | not done |
| progressions/lseries/partial-sums.md | `norm_partialSum_sub_LFunction_one_le` | not done |
| progressions/lseries/trivial-character.md | `norm_LFunction_one_add_le` (proposed) | not done |
| progressions/lseries/complex-lower-bound.md | `norm_LFunction_one_ge_of_sq_ne_one` | not done |
| progressions/quadratic-fields/quadratic-field.md | `QuadField`, `finrank_quadField` (proposed) | not done |
| progressions/quadratic-fields/discriminant-bound.md | `abs_discr_quadField_le` (proposed) | not done |
| progressions/quadratic-fields/signature.md | `nrPlaces_quadField_of_neg`, `nrPlaces_quadField_of_pos` (proposed) | not done |
| progressions/quadratic-fields/roots-of-unity.md | `torsionOrder_le_six_of_finrank_eq_two` (proposed) | not done |
| progressions/quadratic-fields/imaginary-regulator.md | `regulator_quadField_of_neg` (proposed) | not done |
| progressions/quadratic-fields/real-regulator.md | `log_goldenRatio_le_regulator` (proposed) | not done |
| progressions/quadratic-fields/residue-bound.md | `dedekindZeta_residue_ge` | not done |
| progressions/ideal-counts/ideal-count.md | `idealCount` (proposed, def) | not done |
| progressions/ideal-counts/multiplicative.md | `idealCount_mul` (proposed) | not done |
| progressions/ideal-counts/local-factors.md | `idealCount_prime_pow` (proposed) | not done |
| progressions/ideal-counts/splitting-law.md | `idealCount_prime_quadField` (proposed) | not done |
| progressions/ideal-counts/zeta-factorization.md | `dedekindZeta_quadField_eq` (proposed) | not done |
| progressions/real-characters/classification.md | `exists_legendre_of_real_char` | not done |
| progressions/real-characters/real-lower-bound.md | `norm_LFunction_one_ge_of_sq_eq_one` (proposed) | not done |
| progressions/counting/mertens.md | `abs_sum_vonMangoldt_div_sub_log_le` (proposed) | not done |
| progressions/counting/principal-character.md | `sum_coprime_vonMangoldt_div_ge` (proposed) | not done |
| progressions/counting/twisted-sum-bound.md | `norm_LFunction_one_mul_twistedSum_le` (proposed) | not done |
| progressions/counting/uniform-twisted-bound.md | `norm_twistedSum_le` (proposed) | not done |
| progressions/counting/orthogonality.md | `sum_filter_modEq_eq_avg` (proposed) | not done |
| progressions/counting/prime-powers.md | `sum_vonMangoldt_div_not_prime_le` (proposed) | not done |
| progressions/counting/twentytwo-primes.md | `twentytwo_primes_of_twisted_bound` | not done |
| progressions/effective-dirichlet.md | `effective_dirichlet` (proposed) | not done |
| progressions/catalogue-instance.md | `catalogueBound8` (proposed), proving `ZInQ.CatalogueBound8` | not done |

Owners (in the notes): pp-lseries for `lseries/` (steps 1, 2); pp-quadfield for
`quadratic-fields/`; pp-idealcount for `ideal-counts/` except the factorization; pp-realchar
for the classification; pp-mertens for `counting/` and the effective theorem. Not yet assigned:
the zeta factorization (step 3.4) and the real-character lower bound (step 3.5 assembly);
the instance belongs to step 5.

Restated articles (frontmatter `lean`/`statement`/`proof` left alone):
main/catalogue-bound.md, main/main-theorem.md, main/README.md, roadmap/README.md,
size/README.md, size/cutoff.md, size/constants/{README, catalogue-bounds, catalogue-size,
formal-multiple-size, r-equals-d, closed-comparisons, small-constant-bounds}.md,
size/majorants/admissible-cutoff.md, coverage/README.md (Section 12 row),
sources/size-locators.md (BMOR note).

## Statement corrections and changed constants (against the plan)

- Twisted sums: `|S_χ(x)| ≤ 2^24 q^5` for every nonprincipal `χ` and `x ≥ 1` (uniform-twisted-bound),
  instead of `C₁ q^(5/2)`. Proof: `M = log q + 3 ≤ 3√q`, then `256·3^7·21 q^5 < 2^24 q^5`
  (complex) and `840 q^(5/2)` (real). This avoids bounding `(log q + 3)^7/q^(3/2)`.
- The twisted sum article is stated as a product, `|L(1,χ)| |S_χ(x)| ≤ M² + 12q`, so it needs no
  nonvanishing; `12q = 2q·6` from `ψ(x) ≤ (log 4 + 4)x ≤ 6x` (`Chebyshev.psi_le_const_mul_self`).
- Mertens: `C₀ = 6`, hence the principal-character bound `log(x/y) − 12 − log q` (the plan has
  `2 log q`; `log q` suffices since `Σ_{p|q} log p/(p−1) ≤ log q`).
- Prime powers: an absolute bound `Σ_{n≤x, n not prime} Λ(n)/n ≤ 3` (telescoping with
  `log m ≤ √m`) replaces the plan's `O(log y/√y)`; each prime contributes at most `1/e`.
- Count: at least 22 primes `≡ a` in `(y, x]` whenever `1 ≤ y ≤ x` and
  `log(x/y) ≥ q(2B + 11) + 12 + log q` (since `21/e + 3 < 11`).
- Effective theorem: `q₀ = 2^16` (plan: `≤ 2^64`), interval `(q², 2^(q^8))` with `y = q²`
  (plan: `y = q^8`); `W > 10^5 > 2^16`, so small-constant-bounds' lower bound on `W` is used again
  (its remark is updated).
- Real characters: `|L(1,χ)| ≥ 1/(40 q^(3/2))` (proof gives `log φ/18 ≈ 0.0267`).
- Real regulator: the plan's argument ("a unit `ε > 1` is `(a + b√d)/2` with `a, b ≥ 1`") only gives
  `ε ≥ (1+√2)/2` for `d = 2, 3`. The article uses the trace instead: `ε + ε' ∈ ℤ`, `εε' = ±1`, so
  `ε − 1/ε ≥ 1` or `ε + 1/ε ≥ 3`, hence `ε ≥ φ`. Same bound `R_K ≥ log φ`.
- Residue bound stated in `|d|`: `κ_K ≥ log φ / (6√|d|)`; with `|d| ≤ q` this is the plan's bound.
- Classification: "every prime factor of `d` divides `2q`" (equivalent to the plan's "every odd
  prime factor divides `q`", and the form the factorization uses).
- Partial sums at 1: the proof gives `q/x`; the article keeps the plan's `2q/x`.
- Size numerals: `N_s < 2^(2^4613)`, `c_* < 2^(2^4617)`, `ℓ < 2^(2^4623)`, `H_max < 2^(2^4096)`,
  `H_cat ≤ 2^(22W^9)`, index bound `2^(2^4618)`; closed comparisons 1–2 become
  `433 + 22·2^4608 < 2^4613`, `4 + 1262628 + 16104·2^4608 < 2^4623`, `2 + 10·2^4613 < 2^4617`.
  (The plan's general formula `K+518` would give `4614` for `N_s`; the direct estimate gives `4613`.)
- Main theorem: its fourth hypothesis now reads "twenty-two primes below `2^(W^8)`", with a link to
  the instance article; main/catalogue-bound.md states the `W^8` version.

## Lemmas beyond the plan's list

`trivial-character` (`|L(1+x, χ₀)| ≤ 1 + 1/x`), `ideal-count` (the counting function as a
definition), `prime-powers`, `uniform-twisted-bound`, and the split of the regulator into the
imaginary and real cases.

## Problems

- `autoform migrate article-ids blueprint --write` also assigns ids to every container README
  that lacks one (about 30 files in other chapters). I reverted those and kept ids only in
  `progressions/`.
- Until cat-rewire lands, main/catalogue-bound.md and the restated size articles carry
  `statement: formalized` with `lean:` names whose Lean statements still use `2^(W^3)` and the
  old numerals. The lead should update `lean:` (for example `ZInQ.CatalogueBound8`) when the
  rewiring is merged.
- Marcus's chapters are cited by topic (2: number rings, 3: prime decomposition, 5: units,
  7: zeta and class number formula); I did not check chapter titles against the book.

## Suggestions for the next agent

- The constants are linked: changing Mertens' `6` changes the `12` in the principal-character
  and count articles; using `log p/p ≤ 1/2` instead of `1/e` needs `11 → 14` in the count and the
  effective theorem (the margin at `q ≥ 2^16` is ample). Keep article and Lean in step.
- The zeta factorization and the real lower bound need an owner once 3.1–3.3 land.
- Pick one convention for quadratic fields (Mathlib's `QuadraticAlgebra ℚ d 0`, or an arbitrary
  degree-2 number field with a chosen `√d`) and record it in the note of quadratic-field.md.
