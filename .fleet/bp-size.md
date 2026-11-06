# bp-size report: the cutoff and polynomial size (Section 12)

Branch `wip/bp-size`. Owned paths: `blueprint/roadmap/size/`, `blueprint/sources/size-locators.md`,
and the implementation notes of the articles below. Nothing else was edited.

Validation: `autoform check blueprint` passes (175 articles, 443 dependencies). `autoform audit
blueprint` reports no finding in the owned paths; its remaining errors are the coverage rows
(`declared-coverage-gap`, not mine) and `missing-source-link` on other chapters' interface stubs
(assembly, compiler, multiplication). No Lean process was run: Mathlib names in the notes were
checked by grep in `.lake/packages/mathlib` (v4.35.0) and the Lean 4.35.0 `Init` sources.

## Articles (37 leaves, 5 containers)

Interface articles (stub ids kept, `not_ready` removed):

- `size/cutoff.md`: Proposition 12.1. Assuming CAT: R = D, T = (96·10^13)^13 D^{2210 G0² D³}, and
  T < 2^{2^{2^9013}}. Without CAT: 1 ≤ M0 ≤ N_s^10, and M0 is a successful formal multiple.
  Other chapters (multiplication, assembly) should link this article.
- `size/syntax-bounds.md`: assuming CAT, P_* has 292,890,231,905 variables, degree ≤ (T+1)^2048 < 2↑↑7,
  and coefficients ≤ 2^{(T+1)^2048} < 2↑↑8.

`size/constants/` (bounds for the fixed constants):
- small-constant-bounds (FINITE), catalogue-bounds (uses CAT), catalogue-size (N_s < 2^{2^2054},
  ℓ < 2^{2^2063}), formal-multiple-size (c_* < 2^{2^2059}), d-bounds (2^{2^8008} < D < 2^{2^9010}),
  r-equals-d, t-identity (C_cm < 2^{50000D²} < Q^17, closed form of T), t-bound.

`size/formal-multiple/` (the least formal multiple succeeds at an index ≤ N^10, for every N ≥ 1):
- odd-primes (background), odd-coefficient-extraction, reduction-homomorphism (background,
  Silverman VII.2.1), trivial-point-count, filtration (background), bad-place-reduction (FINITE
  part), dyadic-start (FINITE, small), reduction-orders, formal-multiple-existence.

`size/norms/` (Section 12.1, first part):
- l1-norm (def), l1-norm-estimates (background), substitution-bounds, pair-norm,
  division-polynomial-size, quadratic-heights, coordinate-heights, guard-size, constructor-bounds.

`size/majorants/` (Section 12.1, second part):
- syntax-height (def, includes the majorant predicate Maj_B), majorant-rules, node-majorant,
  recipe-majorant, template-heights (FINITE), recipe-heights, admissible-cutoff,
  degree-coefficient-bound, tower-comparison.

Sources: `blueprint/sources/size-locators.md` (Section 4 constants, Section 2.2 LFM, Section 12
opening, Proposition 12.1 and three parts of its proof, four parts of Section 12.1, Silverman,
BMOR, and the companion proof, height traversal and saved constants artifacts).

## Finite computations

| Article | Decidable statement | Size | Method |
| --- | --- | --- | --- |
| small-constant-bounds | `primorial 324 < 2^433 ∧ 10^5 < 4·primorial 324 < 2^435 ∧ 2^2000 < 324! < 2^2250 ∧ 116064000000 < 2^37` | 433-bit product, 2241-bit factorial | kernel `decide` after rewriting with the syntax chapter's `primorial_324_eq`; the factorial part copies upstream's private `ExplicitCutoffBounds.factorial_bounds` (kernel `decide`) |
| bad-place-reduction (part 1) | eight congruences mod 7 (residues of P0 at (d) are (2,6), ρ(A)=0, (2,6) nonsingular on y²=x³) | small integers | kernel `decide` |
| dyadic-start | 2-adic valuations of 1641/8, 145, 15465/4, 87483/32 are −3, 0, −2, −5 | tiny | `norm_num`/`decide` on `padicValRat` |
| template-heights | heights of the 23 constructed templates ≤ (18,21,12,12,25,24,79,169,207,17,4,214,223,230,9,34,249,43,17×5); 173 const nodes, all `abs < 2^69`; 50 constructor nodes, with fixed = ref ℓ, guard = ref T, psi indices ∈ {ε, ε±1, 2ε : ε ∈ {c_*, integer_constant_0..4}} (syntactic) | about 7,100 nodes | kernel `decide` on a Boolean checker over `Syntax.library`; fallback `native_decide` (milestone 1), then node lists pinned as literals plus per-template `rfl` against `Prog.dag` (milestone 2) |

Small closed literal comparisons inside proofs (for example `(96·10^13)^13 < 2^650`,
`2210·G0² < 2^86`, `22·2^2048 + 433 < 2^2054`, the division-polynomial base cases
`3·3^4+6·27143·9+27143² < 2^30`, `2(3^6+…+27143³) < 2^46`, `16·81456² < 2^38`, and
`2↑↑4 = 65536`) are kernel `decide` on literals. No proof evaluates D, T, H_cat, N_s, M0, c_*, ℓ,
Q or c_3.

## Extra hypotheses

None beyond the five. The chapter uses CAT (`ZInQ.CatalogueBound`) for H_max, H_cat, N_s, ℓ,
R = D, the closed form of T, and everything downstream. The formal-multiple existence does not
use CAT or MW.

Inherited inputs that are not yet formal theorems:
- coordinate-heights uses the model chapter's background theorem *Division polynomials compute
  multiples* (`model/field/division-polynomial-multiples.md`), equivalently the syntax chapter's
  proposition `ZInQ.DivisionPolynomialMultiplication`. Until it is formalized, the guard size
  bound, and so the coefficient bound, depends on it.
- reduction-homomorphism (Silverman VII.2.1) and filtration (the elementary form of the
  formal-group facts) are background articles with real Mathlib gaps. Mathlib v4.35.0 has
  `WeierstrassCurve.reduction` only at curve level, with no reduction map on points and no formal
  group. Both are formalizable (estimated several hundred lines each) and are not stated as
  hypotheses.

## Manuscript issues and deviations (all recorded in the articles)

1. **Hasse's bound is not needed.** The trivial count #Ẽ(k) ≤ 2|k|+1 gives (2p+1)² ≤ p^6 at two
   split primes and 2p²+1 ≤ p^6 at an inert prime, so m0 ≤ N_s^6 still holds. The manuscript's
   "(p+1)² < p³" is correct but unnecessary.
2. **Formal groups replaced by an elementary filtration lemma.** In t = x/y, w = 1/y coordinates
   (Washington §8.1 style), it holds on K0 with the 𝔭-adic valuation, with no completion. The
   manuscript's dyadic step uses the logarithm isometry with equality
   v_s(z([2]Q)) = v_s(z(Q)) + 2; only "≥" is used.
3. **Extraction at 2 is exact.** The model chapter's formula v_s(c0+c1 s) = min(2v_2 c0, 2v_2 c1 + 1)
   gives v_2 ≥ 3 + 8v_2(N_s) directly, where the manuscript "loses at most three units".
4. **The existence argument works for every N ≥ 1** and does not use that P0 has infinite order,
   since the ξ convention covers O. The manuscript's remarks about definedness of earlier search
   steps are not needed with the total definition of LFM.
5. **"Checked facts" that are really symbolic.** Section 12.1 lists "absolute values of all literal
   fixed constants and all occurring division-polynomial indices are at most T" among facts
   "checked for the actual saved expression". It cannot be checked by evaluation (it involves c_*
   and T); it is proved symbolically in admissible-cutoff. The bound on the fixed node's value ℓ,
   which the constructor bound needs, is not listed explicitly in the manuscript; the companion
   proof (S26 §3) includes it. Here ℓ < 2^{2^2063} < D ≤ T.
6. **The coordinate-height step has margin.** At most four levels of field operations are needed
   for x([n]P0), y([n]P0); the manuscript says "at most eight". Eight is used, as in the
   manuscript, and still gives K = 2^30 (T+1)^3. The base size computed here is
   2^{135(|m|+1)^3} against the companion's 2^{160(2T+1)^3}, which is consistent.
7. **CAT replaces BMOR.** The progression estimate (BMOR) and W > 10^5 are not needed: CAT states
   the 22-primes-per-class conclusion. W > 10^5 is kept in small-constant-bounds for
   faithfulness.
8. **The T bound route differs slightly.** t-bound bounds the closed form directly
   ((96·10^13)^13 < 2^650, D^{2210G0²D³} < 2^{D^5}, D^8 < 2^{2^9013}), as upstream's
   `ExplicitCutoffBounds.t_lt_triplePower` does, instead of the chain E0 < D³, log2 Q < D^5,
   log2 A_ht < D^7. The conclusion log2 T < D^8 is the same.
9. **Recipe constraint counts** (476, 293,622) are derived from the translation and the
   natural-circuit shape, not traversed. The manuscript's safe height four for the model wrappers
   is used (not the companion's height two), as the manuscript says.

## Interface requirements on other chapters (open questions)

- **natural-circuit-statistics (syntax chapter):** admissible-cutoff needs |c_3| < 10^3181317
  ("c_3 has 3181317 decimal digits", item 3 of that article). That article's implementation note
  plans to check only distinctness of c_3. Its Lean statement must include the digit bound, or
  the compiler chapter must supply a symbolic bound on the program literal. Either way it must
  stay far below D.
- **Syntax chapter:** template-heights assumes the constructed node lists (`Prog.dag`) mirror the
  saved specification's, so that the listed heights hold. If they differ, the check computes the
  actual heights, and the final comparison still holds for any root height h with
  8h ≤ 2^9013 (the tower slack is enormous). Only the stated value 256 would change.
- **Syntax chapter:** `Syntax.IsFormalMultiple` should be a named predicate. It is the body of
  the `sInf` in `leastFormalMultiple`, which `formal_multiple_succeeds` exports.
- **Assembly / Hypothesis H matching:** `ZInQ.heightQ` in ZInQKernel/Hypotheses/Height.lean uses
  `Real.rpow`, while `Syntax.Q` is a natural number. The cast lemma relating them belongs to
  whoever identifies A_ht with H_6(S; D). The cutoff note records this.
- **Model chapter:** the general reduction-homomorphism article (any odd prime, including inert
  and the cusp at (d)) subsumes item 1 of `model/descent/reduction-torsion.md`. Formalizing it
  once serves both chapters.

## Upstream reuse

- `ZInQ.ExplicitCutoffBounds.t_lt_triplePower` gives t-bound exactly.
  `ExplicitCutoffBounds.d`, `g0` and `t` match `Syntax.D`, `G0` and the closed form of T.
  `factorial_bounds` and `d_upper` are private, so their proofs are copied.
- `ZInQ.NumericalTowerBounds.degree_bound_of_cutoff_bound`, `coefficient_bound_of_cutoff_bound`,
  `triplePower_9014_lt_tower_seven` and `quadruplePower_9014_lt_tower_eight` give
  tower-comparison exactly.
- `ZInQ.CoefficientAllocation` does not apply (it concerns multilinear ZMod 2 products).
