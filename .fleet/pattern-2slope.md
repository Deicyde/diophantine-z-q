# pattern-2slope: report

Task: simplify hypothesis 22P, following the research note `docs/research/rs-pattern.md`
(merged from `wip/rs-pattern`). Build: `lake build ZInQKernel` succeeds;
`python3 scripts/check_target.py` reports that `FrozenTarget` is unchanged; `#print axioms` of
`exists_bounded_integer_polynomial_defining_integers_of` and of the new
`..._of_twoSlopePattern` gives `[propext, Classical.choice, Quot.sound]`. No `sorry`.

## Result in one paragraph

The note's claims about the Lean are correct (checked). `TwoSlopePattern` (22P₂) is defined.
The theorem `slopeRepresentation_of_twoSlopePattern` derives from it exactly what completeness
consumes, and the main theorem is proved a second time with `h22 : TwoSlopePattern`, for the
same polynomial. **Step 4 fails:** `FixedPrimePattern → TwoSlopePattern` does not follow, for the
reasons given below. So the main theorem keeps `h22 : FixedPrimePattern`, and the 22P₂ version
is a second theorem. To avoid duplicating the chain, the internal chain from `slopes_of_int` to
`Assembly.assembly` now takes the slope-level interface `Mult.SlopeRepresentation` (the note's
(SR)). Both hypotheses imply it.

## Table

| Article path | Lean name | Status |
| --- | --- | --- |
| `blueprint/roadmap/main/prime-pattern.md` (22P, unchanged) | `ZInQ.FixedPrimePattern` | statement (hypothesis), unchanged |
| new: 22P₂ (no article yet) | `ZInQ.TwoSlopePattern` (`Hypotheses/PrimePattern.lean`) | definition (hypothesis) |
| new: good slope prime | `ZInQ.GoodSlopePrime`, `ZInQ.GoodPatternPrime.goodSlopePrime` | definition, proved |
| `blueprint/roadmap/multiplication/completeness/pattern-slopes.md` | `ZInQ.Mult.pattern_slopes` (unchanged statement), `ZInQ.Mult.SlopeRepresentation`, `ZInQ.Mult.slopeRepresentation_of_fixedPrimePattern` | proved |
| new: slopes from 22P₂ | `ZInQ.Mult.slopeRepresentation_of_twoSlopePattern` (`Multiplication/Completeness/TwoSlope.lean`) | proved |
| new: the constant slope `-10` | `ZInQ.Mult.goodSlope_neg_ten` | proved |
| new: main theorem under 22P₂ | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_twoSlopePattern` (`Main.lean`) | proved |

## Step 1: checking the note against the Lean

All claims checked by reading the code. Two of them are now also checked by Lean proofs.

- **22P is destructured only in `Mult.pattern_slopes`.** Its single caller is `slopes_of_int`
  (`Core.lean`), with `B₀ = 0`.
- **Clauses of 22P that are used:**
  - from `GoodPatternPrime`: `p` prime, the root `r` of `X² − 2`, `75 ∓ 53r ≠ 0`, and
    `gcd(d₁,d₂) = 4` (in `exists_shift`);
  - the multipliers `ε k` with `k ∈ 𝓚`, which bound the valuations at `S_b`;
  - the values `v` and `u_j − v`, for the old-prime valuations; `v` is also used once at a new
    prime (`hv01`);
  - `B₀`, only to keep the pattern primes outside `S_b`. `GoodSlope`'s `B₀ < p` is discarded
    downstream.
- **Clauses that are never used:** `p ≠ 2` and `p ∤ d₁d₂`. This is now enforced in Lean:
  `GoodSlope.contact` asks only for `GoodSlopePrime`.
- **Is `−10` a valid slope?** Yes: `goodSlope_neg_ten : GoodSlope 0 (-10)`.
  - The contact values are `−10, 5, 10, 14, 20, 50`, so there is no odd contact prime outside
    `S_b`, and `P = ∅`.
  - `F(−10)/(−11)⁸ = −2⁶5⁶7/11⁸`. Its valuations at `q ≤ 324` are at most 13, below
    `8B_q = 32`, and they vanish at catalogue primes.
  - `|v_q(−11)| ≤ 1 ≤ B_q`.
- **A small correction to the note (§1.2):** with the two-slope pattern, `v` need not have
  `v_q(v) ∈ {0,1}` at new primes. The contact-valuation-one argument needs only that each contact
  numerator is `±` a prime: `v_q(t − c) = v_q(u − cv) − v_q(v) > 0` forces `v_q(u − cv) = 1` and
  `v_q(v) = 0`.

## Step 2: the statement of 22P₂ (statement corrections)

```lean
def GoodSlopePrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ r : ZMod p, r ^ 2 = 2 ∧ (75 - 53 * r : ZMod p) ≠ 0 ∧ (75 + 53 * r : ZMod p) ≠ 0 ∧
    Nat.gcd (pointCount p (-(75 - 53 * r) ^ 2)) (pointCount p (-(75 + 53 * r) ^ 2)) = 4

def twoSlopeValues (A u v : ℤ) : List ℤ :=
  ([0, -15, -20, -24, -30, -60] : List ℤ).flatMap fun c => [u - c * v, u - (A + 10 - c) * v]

def TwoSlopePattern : Prop :=
  ∀ A : ℤ, ∃ u v : ℤ, v ≠ 0 ∧
    (∀ x ∈ twoSlopeValues A u v,
      GoodSlopePrime x.natAbs ∧ 324 < x.natAbs ∧ x.natAbs ∉ catalogueSet) ∧
    ∀ x ∈ [v, u - v, u - (A + 9) * v], ∀ q : ℕ, q.Prime →
      (q ≤ 324 → padicValInt q x ≤ 4) ∧ (q ∈ catalogueSet → padicValInt q x ≤ 1)
```

The note's 22P₂ (§2.5) implies this statement (argued on paper below, not proved in Lean). It
differs from the note's version as follows; each change weakens the hypothesis:

- **Goodness.** The values need only be good *slope* primes, i.e. without `p ≠ 2` and
  `p ∤ d₁d₂`.
- **Sign and size.** Each value is a good prime up to sign (`natAbs`). It must be `> 324` and
  outside the catalogue, rather than `> max 𝓗`.
- **The common difference.** The note asks for `v = 8 P_s w` with `w` odd, `v_q(w) ≤ 3` for odd
  `q ≤ 324`, and no catalogue square dividing `w`, `u − v` or `u − (A + 9)v`. The Lean statement
  asks only that `v`, `u − v` and `u − (A + 9)v` have valuation `≤ 4` at `q ≤ 324` and `≤ 1` at
  catalogue primes.
  - The note's form implies this: `q | v` and `q ∤ u` give `v_q(u − v) = 0`.
  - These conditions are exactly `GoodSlope`'s condition 2 for the slopes `u/v` and
    `A + 10 − u/v`, given that the twelve values are units at `S_b`.
- **Old primes.** `u ≠ v` and `u ≠ (A + 9)v` are not assumed. They follow because `16v` is
  never prime.

## Step 3: what the consumer gets

- `Mult.SlopeRepresentation := ∀ A : ℤ, ∃ t : Fin 3 → ℚ, ∑ j, t j = A ∧ ∀ j, GoodSlope 0 (t j)`.
- `slopeRepresentation_of_twoSlopePattern` uses the slopes `t = (u/v, ((A+10)v − u)/v, −10)`.
  - The general lemma `goodSlope_of_primeValues` covers both non-constant slopes: if the six
    contact numerators are `±` good slope primes outside `S_b`, and `v` and `u − v` are bounded
    by `B_q` on `S_b`, then `u/v` satisfies `GoodSlope 0`.
  - For the second slope, its numerators are the negatives of the other six pattern values.

## Step 4: why `FixedPrimePattern → TwoSlopePattern` does not follow

The two statements are existence claims for **different linear systems in primes**. Neither is
an instance of the other.

- **22P** gives, for each `A`, a point `(u₁, u₂, v)` of a 3-variable system. Its values are
  `u_j − bv`, where `u₃ = Av − u₁ − u₂` is coupled to `u₁ + u₂`. Each value is `ε k p` with a
  catalogue multiplier `k = d h`, which is never `1`.
- **22P₂** asks for a point `(u, v)` of a 2-variable system: twelve values
  `u − c′v`, `c′ ∈ 𝒞 ∪ (A + 10 − 𝒞)`, each `±` a prime with no multiplier.
- No specialization of 22P's three variables produces 22P₂'s pattern:
  - the 22P values `u₃ − cv = Av − u₁ − u₂ − cv` involve `u₁ + u₂`, not a single `u`;
  - every 22P value carries a factor `h ∈ 𝓗` (`h > 324`), so it is never `±` a prime.
- Deriving one statement from the other would need the analytic machinery (the Green–Tao–Ziegler
  count) that proves both. Lean has no such derivation.

As the task asked, the main theorem stays on `FixedPrimePattern`, and
`exists_bounded_integer_polynomial_defining_integers_of_twoSlopePattern` is added. (Both 22P and
22P₂ are expected to follow from the same GTZ machinery; 22P₂ is the simpler, translation-invariant
pattern.)

## Changes to existing declarations

- **`GoodSlope.contact`** (`PatternSlopes.lean`) asks for `GoodSlopePrime p` instead of
  `GoodPatternPrime p`. This weakens the structure.
  - `exists_shift` (`SlopeCompleteness.lean`) is stated with `GoodSlopePrime`.
  - `goodSlope_of_values` converts with `GoodPatternPrime.goodSlopePrime`.
  - The statement of `pattern_slopes` is unchanged.
- **The hypothesis argument `h22`** has type `Mult.SlopeRepresentation` (was `FixedPrimePattern`)
  in:
  - `Mult.slopes_of_int` (which now just calls `h22 A`) and `Mult.completeness_core`;
  - `Mult.multiply_complete`;
  - `Mult.multiplication_exact` and `Mult.multiplication_existsUnique`;
  - `Assembly.main_branch_eq`, `Assembly.value_relation_iff` and
    `Assembly.exists_value_relation_iff`;
  - `Assembly.Pstar_spec` and `Assembly.assembly`.

  In `Assembly/Top/Assembly.lean` only the two `(h22 : …)` binders changed. The docstrings there
  still say "22P", to keep the merge with pp-final (removal of `hCAT`) conflict-free apart from
  those binder lines.
- **`Main.lean`.**
  - The four existing theorems keep `h22 : FixedPrimePattern`. `_of_addMulBound` passes
    `Mult.slopeRepresentation_of_fixedPrimePattern h22`.
  - New theorem `exists_bounded_integer_polynomial_defining_integers_of_twoSlopePattern`, with H,
    PC, 22P₂ and CAT₈.
  - One paragraph added to the module docstring.
  - When merging with pp-final, drop `hCAT` from the new theorem as well.
- **New file** `Multiplication/Completeness/TwoSlope.lean`. It is imported by `Core.lean` and by
  the root `Multiplication/Completeness.lean`.

## Lemmas added beyond the task items

In `ZInQ.Mult` (`TwoSlope.lean`):

- `padicValInt_eq_zero_of_natAbs_lt_twoSlope`
- `padicValInt_neg_twoSlope`
- `one_le_Bp`
- `goodSlope_of_primeValues`
- `not_isOddContactPrime_neg_ten`
- `goodSlope_neg_ten`
- `not_prime_natAbs_sixteen_mul`

All names were grepped for uniqueness.

## Problems

- None in Lean.
- The swap in step 5 was not done, because step 4 fails mathematically (see above).

## Suggestions for the next agent / the lead

- **Choosing the trust boundary.** The project can keep 22P (manuscript fidelity) or switch the
  headline theorem to 22P₂. The latter is a one-line change in `Main.lean`, since the chain takes
  `SlopeRepresentation`.
- **Blueprint.**
  - Add a leaf for 22P₂ and for `slopeRepresentation_of_twoSlopePattern`.
  - Update `pattern-slopes.md` and `slope-completeness.md`: condition 3 of `GoodSlope` now asks
    for `GoodSlopePrime`, without `p ∤ d₁d₂`.
- **Further weakening.** The relaxation `gcd(d₁, d₂) | c_*` from note §1.4 needs a one-lemma
  change to `shift_choice'`, and then `GoodSlopePrime` could be weakened again.
- **Catalogue removal.** The note's R2 (removing the catalogue, hence CAT) would let 22P₂ drop
  its catalogue clauses. It changes the polynomial; that is the lead's decision.
- **Optional.** Define the note's literal 22P₂ (`v = 8 P_s w`) and prove that it implies
  `TwoSlopePattern`. This is elementary; the argument is in "Step 2" above.
