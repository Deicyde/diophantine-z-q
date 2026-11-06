# rv-size: adversarial review of the size chapter (Section 12)

Branch `wip/bp-size`, reviewing the writer's commit `5d68f86` and report `.fleet/bp-size.md`.
I edited only owned paths: `blueprint/roadmap/size/`, `blueprint/sources/size-locators.md`
(unchanged) and the implementation notes of size articles.

Validation after the fixes: `autoform check blueprint` reports OK (177 articles, 455
dependencies). `autoform audit blueprint` reports nothing in the owned paths. The remaining
audit errors are the `declared-coverage-gap` row and `missing-source-link` on the assembly,
compiler and multiplication interface stubs; none of them is mine to fix. One Lean run
(load 34, 112 GB available): a scratch file checked the two new finite statements and three
Mathlib names, then I deleted it.

## What I checked

- I re-read lines 6272-6442 and 377-403, plus Section 2.2 (lines 238-252), the companion proof
  `construction/z-in-q-polynomial-size-bound-proof.txt`, `bound-ordinary-integer-polynomial.py`
  and its JSON output, and `library.fixedConstants` / the constructor nodes of
  `ordinary-integer-definition.json`.
- **Python recomputation of every closed numerical claim.** This covered:
  - the bit lengths of P_s (433), W (435) and 324! (2241);
  - (96·10^13)^13 < 2^650 and 2210·G0² < 2^86;
  - the division-polynomial base-case norms;
  - the even and odd cubic slacks, re-derived by hand;
  - the constants 65536·1281 < 2^27 and 4·3181317 < 2^24;
  - the bad-place congruences mod 7;
  - the 2-adic valuations of the coordinates of P0.
- **Saved specification against the article.** I checked the following against
  `ordinary-integer-definition.json`:
  - the 23 template heights and the 7 recipe heights and constraint counts;
  - the 173 const nodes, with max bit length 69, so every |c| < 2^69;
  - the 50 constructor nodes: 1 `fixed_integer` (ref ell), 1 guard (ref T), and 48 psi nodes
    whose indices are exactly ε, ε±1, 2ε for ε ∈ {cstar, integer_constant_0..4};
  - integer_constant_0..4 = 4, 2, 3, c_3, 1399.

  All of these match the template-heights article.
- **Step-by-step proof checks:**
  - the majorant closure rules, including the h = 0 and k = 0 cases;
  - the recipe-height arithmetic;
  - the filtration lemma: the slope formula, the cubic in t and the valuation of the third root;
  - the reduction-order bound m0 ≤ N^6 and both extractions (odd places and 2);
  - the normalization step from valuations to N^4 | a, N^4 | b, gcd(c, N) = 1;
  - the t-identity, t-bound, d-bounds, catalogue-size and tower chains.
- **Notes:** I verified the cited Mathlib names by grep in `.lake/packages/mathlib` and the
  Lean 4.35.0 `Init` sources, and the upstream names in `lean/ZInQ/ExplicitCutoffBounds.lean`
  and `NumericalTowerBounds.lean`. `t_lt_triplePower`, `degree_bound_of_cutoff_bound`,
  `coefficient_bound_of_cutoff_bound`, `triplePower_9014_lt_tower_seven` and
  `quadruplePower_9014_lt_tower_eight` are public. `factorial_bounds`, `prefactor_bound`,
  `exponent_coefficient_bound` and `arithmetic_bound` are private, as the notes say.

## Fixed

1. **Positivity of N_s, a real gap.** cutoff.md claimed "independently of the catalogue bound,
   1 ≤ M0 ≤ N_s^10", and formal-multiple-existence ended with "apply this to N = N_s ≥ 1".
   Neither article proves N_s ≥ 1. The catalogue is defined through `Nat.nth`, which returns 0
   past the end of a finite set, so without CAT or Dirichlet H_cat could be 0. Then N_s = 0,
   and for N = 0 the success conditions force ξ([m]P0) = 0, so the claim fails.
   - cutoff.md now states the M0 part with N_s ≥ 1 and says that CAT enters only through
     N_s ≥ 1, which Dirichlet's theorem also gives.
   - formal-multiple-existence states the N_s case conditionally on N_s ≥ 1.
   - cutoff now lists catalogue-size and formal-multiple-size under "Proof depends on".
   - In the notes, `M0_bounds` and `formal_multiple_succeeds` take `hNs : 1 ≤ Syntax.Ns`. The
     Dirichlet route cites the verified name `Nat.infinite_setOfPred_prime_and_eq_mod`
     (Mathlib/NumberTheory/LSeries/PrimesInAP.lean:431). The writer's note had claimed
     `Hcat ≥ 1` holds without CAT "as a product of primes", which is false without Dirichlet.
2. **Wrong constant in t-identity.** 4096(1028+5D+84000D²) ≤ 4096·**85033**·D², not 84006
   (1028+5+84000 = 85033). The conclusion < 2^29·D² still holds (4096·85033 = 348,295,168).
   I fixed both the article and the note.
3. **Finite checks isolated.**
   - New leaf `formal-multiple/bad-place-congruences.md` holds the eight congruences mod 7 that
     were embedded in bad-place-reduction. bad-place-reduction now consumes it, and its note
     lost the FINITE tag.
   - New leaf `constants/closed-comparisons.md` collects every closed literal comparison that
     the symbolic proofs had been doing inline. It is linked from the nine consuming articles
     (catalogue-size, formal-multiple-size, r-equals-d, t-identity, t-bound, d-bounds,
     division-polynomial-size, coordinate-heights, admissible-cutoff).
   - I elaborated both exact Lean statements in the notes with `lake env lean`; `decide`
     succeeds in the kernel.
4. **Filtration proof sketch expanded.** I added:
   - why equal t forces equal points: (w1−w2)(1−at(w1+w2)) = 0 with a unit factor;
   - the derivation of the slope formula;
   - the treatment of the third intersection point (w3 = 0 gives O, otherwise
     v(w3) = 3v(t3), so v(x3) ≤ −2r);
   - closure under negation.

   This makes subgroup closure explicit, where the sketch previously asserted it.
5. **Note pointers.**
   - odd-primes cited `Polynomial.X_sq_sub_C`, which does not exist. It now cites
     `X_pow_sub_C_irreducible_of_prime` (FieldTheory/KummerPolynomial.lean:99) or
     `Polynomial.irreducible_of_degree_le_three_of_not_isRoot`.
   - The filtration draft used `[v.IsDiscrete]`, which does not exist for `Valuation`. It now
     uses `[v.IsRankOneDiscrete]`.

## Finite computations (after review)

| Article | Decidable statement | Size | Method |
| --- | --- | --- | --- |
| constants/small-constant-bounds | `primorial 324 < 2^433 ∧ 10^5 < 4·primorial 324 < 2^435 ∧ 2^2000 < 324! < 2^2250 ∧ 116064000000 < 2^37` | 2241-bit factorial | kernel `decide` (after the syntax chapter's `primorial_324_eq`) |
| constants/closed-comparisons (new) | 17 closed ℕ (in)equalities, listed verbatim in the note | ≤ 9011-bit numbers | kernel `decide`, checked |
| formal-multiple/bad-place-congruences (new) | eight `ℤ` congruences mod 7 | < 3·10^5 | kernel `decide`, checked |
| formal-multiple/dyadic-start | four `padicValRat 2` values | tiny | `norm_num`/`decide` |
| majorants/template-heights | 23 heights ≤ table, 173 consts with abs < 2^69, 50 constructor index expressions (syntactic) | ~7,100 nodes | kernel `decide` on the constructed library; fallback `native_decide`, then pinned literals |

No statement evaluates D, T, H_cat, N_s, M0, c_*, ℓ, Q or c_3.

## Extra hypotheses

None beyond CAT. Background inputs that still need formalizing (all formalizable, none stated
as a hypothesis):
- reduction-homomorphism (Silverman VII.2.1 for an integral short Weierstrass model at an odd
  prime of ℤ[√2]). Mathlib has no reduction map on points.
- filtration (the elementary formal-group facts).
- odd-primes (splitting of odd primes in ℤ[√2]).
- coordinate-heights inherits the model chapter's multiplication-by-n formulas
  (division-polynomial-multiples).

## Still needs work (not fixable inside my paths)

- **c_3 digit bound.** The syntax article natural-circuit-statistics states that c_3 has
  3,181,317 decimal digits, but its implementation note plans to check only distinctness and
  `c_3 > 1399`. admissible-cutoff needs `c_3 < 10^3181317`, or any bound far below D. The
  syntax chapter must include it in the Lean statement.
- **`Syntax.IsFormalMultiple`** should be exported as a named predicate by the syntax
  chapter (the body of the `sInf` in `leastFormalMultiple`).
- **Hypothesis H matching (assembly):** the cast lemma `((Syntax.Q : ℕ) : ℝ) = heightQ D`, since
  `heightQ` uses `Real.rpow`.
- **Template-heights fidelity:** the table is that of the saved specification. If the Lean
  construction (`Prog.dag`) produces different node lists, the check must use the actual
  heights. The final tower comparison has enormous slack, but recipe-heights and
  degree-coefficient-bound quote 256 and 2048 explicitly, so they would need restating.
- **Granularity watch:** reduction-homomorphism (estimated several hundred lines) and
  filtration (~300 lines) are at the upper end of PR size. Their notes propose splits
  (subgroup / homomorphism / kernel; subgroup and congruence / multiplication). I did not
  split them, because the statements are coherent single theorems.
- **Model chapter:** reduction-homomorphism subsumes item 1 of
  `model/descent/reduction-torsion.md`; formalize it once.

## Manuscript issues (confirmed, as recorded by the writer, plus mine)

1. Hasse's bound is unnecessary: the trivial count 2|k|+1 gives m0 ≤ N_s^6.
2. The formal group and logarithm isometry are replaced by an elementary filtration on K0.
   Only the inequality v_s(z([2]Q)) ≥ v_s(z(Q)) + 2 is used, not the equality.
3. The extraction at 2 is exact (v_2 ≥ 3 + 8v_2(N_s)), where the manuscript says it "loses at
   most three units".
4. **Positivity of N_s (new).** The bound M0 ≤ N_s^10 needs N_s ≥ 1. The manuscript gets it
   implicitly from Dirichlet ("Dirichlet's theorem ensures termination", line 240), and the
   formalization gets it from CAT or Mathlib's Dirichlet. The manuscript's remarks on
   definedness of earlier search steps (lines 6312-6316) are unnecessary with the total LFM
   definition.
5. **"Checked facts" that are symbolic.** "All literal fixed constants and division-polynomial
   indices are at most T" (line 6373) cannot be a check by evaluation. It is proved
   symbolically in admissible-cutoff. The bound on the fixed value ℓ (< 2^{2^2063} < D) is
   needed but not listed in the manuscript.
6. **"At most eight" field operations.** Four levels suffice, and eight are used as in the
   manuscript.
7. **The T-bound route.** The writer bounds the closed form directly, as upstream's
   `t_lt_triplePower` does, instead of the chain E0 < D³, log2 Q < D^5, log2 A_ht < D^7. The
   conclusion log2 T < D^8 is the same.
8. **The bounded sums of Section 12.1.** The manuscript's "bounded sums treated as in S26" is
   made explicit as rules (5) and (6) of the majorant closure rules, with term counts ≤ 2^20 ≤ B.

## Faithfulness verdict

After these fixes the chapter is faithful to Section 12 and Proposition 12.1, with two
documented deviations:
- **Hypothesis replacements.** CAT stands in for the BMOR progression estimate, and elementary
  replacements stand in for Hasse's bound and the formal-group logarithm. Each replacement
  proves the same or a stronger intermediate inequality and does not weaken a conclusion.
- **Constants and inequalities.** Every constant in the articles matches the manuscript:
  R = D, T = (96·10^13)^13 D^{2210G0²D³} < 2^{2^{2^9013}}, 2^{2^8008} < D < 2^{2^9010},
  c_* < 2^{2^2059}, log2 N_s < 2^2054, M0 ≤ N_s^10, deg f_n ≤ (n+1)^3, ‖f_n‖ ≤ 2^{100(n+1)^3},
  K_* = 2^30(T+1)^3, constructor bounds B^4 / 2^{B^8}, heights 228…256, deg ≤ (T+1)^2048,
  coefficients ≤ 2^{(T+1)^2048}, 292,890,231,905 variables. Strict and weak inequalities
  match the manuscript.

The two substantive defects the writer left were:
- the unproved N_s ≥ 1 behind the "independently of CAT" claim (now stated correctly);
- the wrong intermediate constant 84006 (now 85033; the conclusion was unaffected).

Every proof sketch is now detailed enough for a formalizer. All tower comparisons are
symbolic. The finite checks are isolated with exact Lean forms, and the two new ones are
verified.
