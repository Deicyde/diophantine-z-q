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
