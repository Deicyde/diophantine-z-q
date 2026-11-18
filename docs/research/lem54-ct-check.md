# Lemma 5.4: Cassels–Tate landing check

**VERIFIED: the dry run compiles using only `propext`, `Classical.choice`, and `Quot.sound`.**
The frozen target keeps every other argument and takes the Cassels–Tate pairing for `E_ℓ` in
place of Lemma 5.4. The pairing matches the cited print as a direct instance. The fold remains
with the lead after the #90 squash.

## 1. Dry run

Base: `wip/lemma54-ct-20261118`. [FrozenCT.lean](../../scratch/lem54-ct-check/FrozenCT.lean)
imports the existing `Main` and the pairing module. It reuses `sixContactMin_of_open79 r t l`
and replaces the call to `poleCompleteness_of_restrictedConverseGenuine_final` with
`poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing hRC hCT hB hK`. There is no
new bundle definition and no Mordell–Weil argument. The two printed signatures confirm the
single binder replacement.

`lake env lean scratch/lem54-ct-check/FrozenCT.lean` exited 0. The
[full output](../../scratch/lem54-ct-check/FrozenCT-output.txt) includes both signatures, the
axiom check and the stock `#discharges` report: 33 open hypotheses, 12,093 theorems checked,
20 matches. The command reads the original `frozenTarget` as its baseline. It recognizes the
bridge to the original `h54` from Mordell–Weil and the pairing for all elliptic curves. The
dry-run proof uses the narrower family consumer, whose Mordell–Weil input is proved already.
The command does not treat a replacement headline as a proof of one of the original hypotheses.

## 2. Manuscript check

References are to `diophantine_zq.tex`. Each row gives the mathematical verdict; **VERIFIED** means
the manuscript and the indicated Lean proof or definition were checked in the repository. Here `Fam`
is `ZInQ.Manuscript.SelmerTwoPower.Fam`, `Cofinite` is `ZInQ.Cofinite`, and the manuscript's finite
summand `F` of Sha is called `F'` in `Fam.selmerCorankOne_of_card_selmerAt_one`.

| Lines | Manuscript step and Lean counterpart | Verdict |
| --- | --- | --- |
| L1072–1075 | Over `ℚ` in context, full rational 2-torsion and Selmer dimension 3 mean `#E(ℚ)[2] = 4` and `#Sel₂ = 8`. These are the inputs of `Fam.selmerCorankOne_of_card_selmerAt_one`; `Fam.selmerAt_eq` and `Fam.selmerCorankOne_iff` identify the groups and conclusion with the headline's definitions. `PoleS12.lemma54At_of_casselsTatePairing` supplies the instance at `E_ℓ` via `lemma54At_of_casselsTate`, using `PoleRC.card_ker_two_nsmul_eq_four_M`, `PoleS12.kummerSelmerM`, and `PoleRC.mordellWeil_curve`. | OK |
| L1077 | The finite Kummer sequence gives `8 = 2^r · 4 · #Sha[2]`, i.e. `r + dim Sha[2] = 1`. `Fam.card_selmerAt_eq_mul` at `n = 1` gives the count; `Fam.exists_addEquiv_pi_int_prod_finite` uses Mordell–Weil and `Cofinite.card_quotient_nsmul_range_of_addEquiv` supplies the factor from rational points. | OK |
| L1078 | The decomposition of `Sha[2^∞]` needs finite 2-torsion. `Fam.isPPrimary_shaTwo`, `Fam.torsShaTwoEquiv` and the surjection `WeierstrassCurve.selmerShaMap_surjective` supply the hypotheses of `Cofinite.exists_addEquiv_of_isPPrimary`: finiteness follows from the eight elements of `Sel₂`. | gap filled |
| L1079–1081 | The pairing is alternating and nondegenerate after quotient by the maximal divisible subgroup. `SelmerTwoPower.CasselsTatePairing` states this as biadditivity, alternation and a left radical equal to `divisiblePart`; `le_divisiblePart` and `divisiblePart_divisible` identify that subgroup. | OK |
| L1081–1082 | The pairing on the finite 2-primary summand is nondegenerate. `SelmerTwoPower.casselsTateSquare_of_pairing` kills the divisible factor, rules out contributions from odd-order classes and rules out nonzero divisible elements of the finite summand. This justifies using the quotient pairing on that summand. | gap filled |
| L1081–1082 | The cyclic factors in the finite 2-primary summand occur in pairs, so `dim F[2]` is even. `SelmerTwoPower.isSquare_card_tors_two_of_alternating` splits off paired cyclic factors and proves the needed `IsSquare (#F[2])` by induction. | OK |
| L1082 | Combining the finite count and the square gives `2^(r+t) · s² = 2`. `Fam.two_pow_mul_sq_eq_two` proves `r+t = 1` and `s = 1`. Hence `F[2] = 0` and `F = 0` since a nonzero 2-primary group has a nonzero element killed by 2 (`Cofinite.exists_nsmul_ne_zero_p_nsmul_eq_zero`). The corank proof uses the first conclusion and does not need a separate triviality proof for `F`. | OK |
| L1082–1084 | The unstated final inference is `corank Sel_{2^∞} = r+t`, using the Kummer sequence below. Lean proves this value in `Fam.selmerCorankOne_of_card_selmerAt_one` with `Cofinite.eq_of_pow_mul_eq`: the two formulas for `#Sel_{2^n}` have exponential factors `2^(n·(r+t))` and `2^(n·corank)` and positive, uniformly bounded remaining factors. | gap filled |
| L1082–1083 | The restriction to `F[2]` need not be nondegenerate (on a paired `(ℤ/4)²`, it is zero); `isSquare_card_tors_two_of_alternating` requires nondegeneracy on `F` itself. | OK |
| L1098–1100 | The injection at infinity comes from the finite Kummer injections `WeierstrassCurve.kummerSelmerMap_injective`; the direct limit of `A(ℚ)/2^n A(ℚ)` under multiplication by 2 is `A(ℚ) ⊗ (ℚ₂/ℤ₂)`. Lean uses the finite injections in `Fam.card_selmerAt_eq_mul`, so the tensor map is not constructed on this route. | OK |
| L1101 | The middle term is `Fam.selmerTwoPower`, identified with the headline by `Fam.selmerTwoPower_eq`. Exactness at the middle term follows mathematically by taking the filtered direct limit of the finite exact sequences (`WeierstrassCurve.exact_kummerSelmerMap_selmerShaMap`). Lean uses finite exactness and instead compares the middle groups via `Fam.twoPowerShortExact`, `Fam.range_selmerAtToTwoPower`, `Fam.card_ker_selmerAtToTwoPower_le` and `Fam.card_selmerAt_eq`. | OK |
| L1102 | The right term is the union of the finite torsion targets, with `Fam.shaTwo` and `Fam.torsShaTwoEquiv` identifying it and its finite levels; the finite maps are onto by `WeierstrassCurve.selmerShaMap_surjective`. Their limit is onto. | OK |

For the mathematical direct limit, the groups are built with continuous cochains and discrete
coefficients: a cochain on finitely many copies of the compact Galois group has finite image, so in
the union of the 2-power torsion modules it is already supported at a finite level. The local
conditions are a preimage of the fixed subgroup `Sha` in point cohomology. This identifies the
direct limit with the cohomological Selmer group; the finite-level Lean proof does not assert the
literal short exact sequence with the tensor term. In that proof, finiteness of `Sel_{2^∞}[2]` comes
from `Fam.range_selmerAtToTwoPower` at `n = 1`, so `Cofinite.exists_addEquiv_of_isPPrimary` also
applies to the Selmer group. `Fam.finite_H0_twoPowerCoeff` supplies the uniform kernel bound from
Mordell–Weil.

## 3. Statement check

**VERIFIED against the recorded quotations; verdict: YES, direct instance.** The sole evidence for
this review is [the repository's quotation record](cassels-tate-pairing.md). No additional source
was read.

| Lean clause | What the quoted print supports |
| --- | --- |
| `sha E` and `QZ` | The domain is the usual `Sha(E/ℚ)`: continuous Galois `H¹` of geometric points, with vanishing restriction at every `ℚ_p` and `ℝ` (`SelmerTwoPower.sha`). This is the `Sha(E)` of Poonen–Stoll; the target is the additive quotient `ℚ/ℤ`. Neither group is an auxiliary structure posited by the leaf. |
| `∃ b : sha E →+ sha E →+ QZ` | **STANDARD:** Poonen–Stoll, *The Cassels–Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999), 1109–1149, Introduction, first paragraph (author's version p. 2), reports Cassels' existence of a pairing for elliptic curves over number fields. A pairing here is biadditive; Lean does not identify a canonical choice. |
| `∀ x, b x x = 0` | The same paragraph states alternation for elliptic curves. The abstract and remarks after Corollary 12 (author's version pp. 1 and 14) corroborate this; Milne's 2nd edition, p. 81, states the rational-divisor polarization criterion, satisfied by the origin divisor on an elliptic curve. |
| `∀ x, (∀ y, b x y = 0) ↔ x ∈ divisiblePart (sha E)` | In the Introduction the pairing descends to the quotient by the maximal divisible subgroup and is nondegenerate there; descent gives containment in the radical, and nondegeneracy gives equality. Alternation makes the two radicals equal; Lean specifies the left one. **STANDARD:** Milne, *Arithmetic Duality Theorems*, 2nd ed., I.6.13(a), p. 82, gives both kernels explicitly for the canonical pairing with the dual on each primary component. It corroborates the kernel clause; the full-group elliptic statement is supported directly by Poonen–Stoll. |
| `CasselsTatePairingCurves` | `ℚ` is a number field, and every tested curve is elliptic by `PoleRC.curve_isElliptic` since its parameter is nonzero. Quantifying over this family only specializes the printed statement. The underlying `CasselsTatePairing E` is a predicate; it is not asserted for singular Weierstrass equations. |

**VERIFIED, citation and strength.** L1079–1081 cites `poonenstoll` for precisely the nondegenerate
alternating pairing after quotient by the maximal divisible subgroup. The bibliography at
L11098–11100 identifies the refereed paper. The next inference about paired finite cyclic factors
is derived in Lean, and the cited paragraph does not have to state Lemma 5.4 or that inference.
Milne is in the bibliography at L11116–11118, but is not the citation at Lemma 5.4. No clause of
`hCT` strengthens the quoted elliptic-curve result: there is no finiteness requirement for Sha, no
claim of a perfect pairing on `Sha[2]`, and no specified pairing or extra compatibility among choices.

Replacement docstring for `SelmerTwoPower.CasselsTatePairing` in
`ZInQKernel/Contrib/OneProof/CasselsTatePairing.lean` (for the integrator):

```lean
/-- **The Cassels–Tate pairing for an elliptic curve `E/ℚ`** (existence form): an alternating
biadditive pairing `Sha(E/ℚ) × Sha(E/ℚ) → ℚ/ℤ` with left radical equal to the maximal divisible
subgroup. This is Cassels' elliptic-curve theorem as stated in Poonen–Stoll, Ann. of Math. (2)
150 (1999), 1109–1149, Introduction, first paragraph (p. 2 of the author's version; see the remarks
after Corollary 12 for alternation). The manuscript cites it at `diophantine_zq.tex` L1079–1081.
Milne, *Arithmetic Duality Theorems*, 2nd ed., I.6.13(a), p. 82, gives the kernels on each primary
component for the pairing with the dual; see p. 81 for alternation under the polarization defined
by a rational divisor. The pairing is not named here. -/
```

## 4. Non-vacuity and compatibility

**STANDARD + VERIFIED.** The printed elliptic-curve theorem gives the premise of
`CTCheck.pairing_on_family` in [NonVacuity.lean](../../scratch/lem54-ct-check/NonVacuity.lean).
Lean verifies the specialization: a positive natural parameter is nonzero in `ℚ`, and the
discriminant `2304 ℓ⁶` is nonzero (`PoleRC.curve_isElliptic`). Neither squarefreeness nor the
congruence is needed for the pairing. `CTCheck.eleven_in_family` verifies that the indexing
conditions really admit a curve (`ℓ = 11`). This uses the published theorem as mathematical
evidence for the premise; the scratch file does not assert an unconditional Lean proof of it.

**VERIFIED, relative compatibility.** Let `P` be the conjunction of the three retained H bundles,
`hRC`, `hB` and `hK`. With the printed theorem, `CTCheck.retained_compatible` proves
`(P ∧ CasselsTatePairingCurves) ↔ P`. Thus any simultaneous realization of the remaining inputs
admits `hCT` with the same curves and definitions. This does not certify the remaining open inputs.
In particular, `hRC` concludes analytic rank one under a corank premise, `hB` supplies modularity, and
`hK` concludes rank one and finiteness of Sha under its modularity and analytic rank premises.
Finiteness is compatible with `hCT`: for finite Sha its maximal divisible subgroup is zero, so the
pairing is nondegenerate on Sha itself (`CTCheck.nondegenerate_of_finite_sha`).

## 5. Proposed kinds row

Proposed rating after reviewer approval: **published, LEAF/LEAF, provenance (b)**. This is a
specialization of the cited print over genuine Sha. The conditional route through Lemma 5.4
is GLUE, and its disappearance from the headline does not discharge the pairing theorem itself.
If entered before the reviewer rates it, use `GLUE/GLUE` with a `pending-review` flag until that
decision is recorded. The row below is the proposed rated form; it has not been entered in
`docs/one-proof/kinds.tsv`.

```tsv
bundle	field	kind	flag	strict	strictest	source	rated_by	packet	label	tier	flag_class	area_issue
frozenTarget	hCT	published	Secondary print: Cassels for elliptic curves as stated in Poonen-Stoll; author-version pagination. Milne I.6.13(a) corroborates the primary kernels. Alternation here is for elliptic curves. Statement checked against recorded quotes only; Cassels 1962 not read.	LEAF	LEAF	Provenance (b): Poonen-Stoll, Ann. of Math. (2) 150 (1999), 1109-1149, Introduction, first paragraph (author version p. 2), cited at diophantine_zq.tex L1081 (bibitem L11098-11100); Milne, Arithmetic Duality Theorems, 2nd ed., I.6.13(a), p. 82 (primary kernels), and p. 81 (rational-divisor polarization).	proposed; reviewer decision required				note	Deicyde/diophantine-z-q#83
```

## Known issues

- **VERIFIED:** In the reviewed manuscript lines there is no false inference after supplying the
  stated details. The decomposition needs finiteness of 2-torsion, the quotient pairing must be
  passed to the finite 2-primary summand, and the proof omits the step that identifies the
  Selmer corank with `r+t`. The Lean proof supplies all three.
- **VERIFIED from the quotation record:** Milne's footnote 17, p. 82, corrects the older blanket
  assertion that the pairing is always alternating. Alternation for elliptic curves is unaffected.
  Nondegeneracy of the restriction to `F[2]` would also be false in general; the manuscript
  explicitly avoids it.
- **UNVERIFIED:** The original Cassels and Tate publications, journal pagination for the
  Poonen–Stoll locator, and the broader section locators in the existing square-property
  docstrings were not checked. The proposed docstring gives only the locators supported by the
  record. In particular, `SelmerCorankFam.lean` names L1077 as the citation; the actual line is
  L1081. The square property is derived from the pairing in Lean.
