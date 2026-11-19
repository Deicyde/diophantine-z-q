# Fowler's singular modulus degree and the CM branch

> **Update (11-19): closed and landed.** j-descent4 proved `abVarFunctionFieldGenusOne` unconditionally and j-descent5
> derived `cmjDegree_of_print_of_genusOne` from it, so `CMPeriodJDescends` is no longer needed: Lean proves
> `CMjDegreePrint → CMjDegree` (`HDec.CMBranch.CMjBridges.cmjDegree_of_print_closed`, `Contrib/OneProof/CMjClose.lean`).
> The cmj-close fold (autofold `TailZ98`, `sixContactMin_of_open91`) replaced the field `cmjDegree` by the leaf
> `cmjDegreePrint` (Fowler 2026, section 2·1, p. 613; rated LEAF). The text below is the earlier scoped stop, kept as written.


**Scoped stop: the analytic j-value of the scheme curve still needs a field-of-definition proof.**
Lean proves `CMPeriodJDescends → CMjDegreePrint → CMjDegree`. The one remaining glue
statement, `CMPeriodJDescends`, says that if `τ` is an actual period of a CM elliptic curve
`E/L` at `σ : L → ℂ`, then `j(τ) ∈ σ(L)`. The curve, the complex base change, the
period, the full multiplier ring, the primitive discriminant, and the degree inequality
use the project's existing objects and are linked by proofs. There is no proof of
`CMjDegreePrint → CMjDegree` alone, no extra leaf, and no fold.

## The printed statement

**STANDARD (published, exact locator; supplied human reading).** Fowler, *Some uniform
effective results on André–Oort for sums of powers in ℂⁿ*, Math. Proc. Cambridge Philos.
Soc. 180 (2026), 607–641, §2·1, p. 613, gives `[ℚ(x) : ℚ] = h(Δ)` for each singular
modulus of discriminant Δ. This is the half over ℚ of the two degree equalities there.
Page 612 specifies Δ from a primitive equation of an upper half-plane quadratic period;
p. 607 specifies Δ by the endomorphism order. See the
[human reading of the publisher PDF](https://github.com/Deicyde/diophantine-z-q/issues/14#issuecomment-6973419601).

**VERIFIED (Lean).** [`CMjDegreePrint`](../../ZInQKernel/Contrib/OneProof/CMjBridgesPrint.lean)
quantifies over `x = j(τ)` and a primitive integral equation with positive leading
coefficient and discriminant Δ. It states the degree using the intermediate field
`IntermediateField.adjoin ℚ {x}`. As in the existing Fowler bridge, an imaginary
quadratic order of discriminant Δ is an explicit parameter, and `h(Δ)` is
`FowlerBridges.properClassNumber` of that order. No equivalence with classes of binary
forms is needed. The j-function is the one from the lattice with generators 1 and τ;
`modularJ_eq` gives the normalized formula `E₄³/Δ_modular`.

## Proved bridges

**VERIFIED (Lean).** The declarations below are in `HDec.CMBranch.CMjBridges` unless
qualified otherwise. All five contribution modules compiled with `lake env lean`.
The [axiom check](../../scratch/cmj-bridges/axioms-output.txt)
lists each theorem and uses only `propext`, `Classical.choice` and `Quot.sound`.

| Step | Theorem | Statement |
|---|---|---|
| Print | `modularJ_eq` | For every upper half-plane τ, `modularJ τ = E₄(τ)³ / Δ_modular(τ)`. |
| 1–2 (for a given equation) | `weierstrass_j_map` | A nonsingular equation `W/L` has `W.j : L` and `σ(W.j) = (W.map σ).j`. The statement does not give an equation for the scheme `E/L`. |
| 2 | `uniformization_exists` | T35 in the original embedding and point form, with lattice of complex dimension `dim E`. |
| 2 | `exists_complex_baseChange_cm` | For each σ, a dimension-one complex abelian variety `B` sits in the pullback square along σ and satisfies `End(B) ≃+* R`. |
| 2–3 | `cmPeriodLattice_proof` | `CMPeriodLattice`: at each σ there is a full period lattice with multiplier ring isomorphic to `R`. |
| 3 | `mem_latticeMultipliers_iff` | For a lattice with basis `s, sτ` and primitive equation `aτ²+bτ+c=0`, its multipliers are exactly `m+n(aτ)` for integers `m,n`, i.e. `ℤ[aτ]`. |
| 3 | `periodDiscriminant_unique` | Any two primitive equations of the same upper half-plane period have equal discriminant. |
| 3 | `periodDiscriminant_iff_orderDisc` | For that lattice with multiplier ring isomorphic to `R`, `PeriodDiscriminant τ Δ ↔ Δ = orderDisc R`. |
| 2–3 | `exists_cm_period` | Each embedded curve has an actual period `τ : ℍ` with `PeriodDiscriminant τ (orderDisc R)`; hence `j(τ)` satisfies the printed singular-modulus predicate at the order discriminant. |
| 3–4 | `toOrder_discr_eq_orderDisc` | The order used for the class number has trace discriminant `orderDisc R`. |
| 4 | `FowlerBridges.card_pic_eq_properClassNumber` (reused) | Its proper ideal class number equals `Nat.card (CommRing.Pic R)`. |
| 5 | `degree_le_of_mem_range` | For `x ∈ σ(L)`, the embedding `ℚ(x) ↪ σ(L)` gives `[ℚ(x):ℚ] ≤ [L:ℚ]`. |
| 4–5 | `card_pic_le_of_singular_modulus` | If `x ∈ σ(L)` is a singular modulus of discriminant `orderDisc R`, the printed degree equality bounds `#Pic(R)` by `[L:ℚ]`. |
| Assembly | `cmjDegree_of_print_of_periodJDescends` | `CMPeriodJDescends → CMjDegreePrint → CMjDegree`. |
| 2 (scratch check) | `group_model_uniformization_check` | The group-model interface `AnalyticUniformizationExists` follows from the proved T35. |
| 2 (scratch check) | `modularJ_surjective_check` | The actual modular j on the upper half-plane is onto ℂ. It is unnecessary for selecting the period in this proof. |

The coordinate uniformization applies to `(E ×_L L̄) ×_{L̄} ℂ` after extending σ.
Pasting the two base changes gives the pullback along σ. T35 follows from the coordinate
uniformization and the proved torsion count, which identifies the dimension.
`cmPeriodLattice_of` then uses the proved GAGA map comparison and rigidity to keep the
full endomorphism ring. In the rank-two lattice, multiplication must preserve both
generators. If the multiplier is `m+nτ`, primitivity gives `a ∣ n`; conversely this
divisibility suffices. The existing Cox lattice proof computes the trace discriminant
in the basis `(1,aτ)`. This gives the p. 607/p. 612 compatibility for the curve obtained
from the actual lattice.

## Exact remaining comparison

In [`CMjBridges.lean`](../../ZInQKernel/Contrib/OneProof/CMjBridges.lean),
`CMPeriodJDescends` only asks for membership in the image of σ, on the actual CM
elliptic curves and actual periods of the row. It mentions neither degrees nor class
numbers. The period witness used by the conditional proof already exists unconditionally.
The missing result is stronger than algebraicity of `j(τ)` over ℚ: it must land in
this particular embedded field, with no passage to a larger field.

**VERIFIED (interfaces).** Mathlib's `WeierstrassCurve` starts with coefficients and
proves naturality of its j under coefficient maps. The vendored period-pair theory
constructs Weierstrass coefficients and a point uniformization from a complex lattice.
Neither interface by itself compares an arbitrary dimension-one `DefFaltings.AbVar`
over `L` with a nonsingular Weierstrass model over `L`, or identifies its lattice
j with that model's algebraic j. No such comparison was found in the allowed import
tree. Surjectivity finds a period for an already specified complex j-value; it
does not supply the field of definition of the j-value of this scheme.

**SPECULATIVE (size and route).** A Weierstrass route needs a genus-one normal-form
construction at the origin over `L`, and comparison of the resulting coordinates
with ℘ and ℘′ on the complex torus. A narrower route could descend the spaces of
functions with poles of orders at most two and three at the origin, then compare
their complex bases with the lattice functions and calculate the invariant. Either
route is a separate scheme and analytic comparison, with several substantial
lemmas beyond the coefficient map formula. A proof of the named membership
statement alone suffices: the conditional theorem then needs only Fowler's equality.

## Counts and dry run

**VERIFIED.** The [discharge scan](../../scratch/cmj-bridges/discharges-output.txt)
shows the new candidate for the live field `OpenResearchLeaves66.cmjDegree` with **both**
`CMPeriodJDescends` and `CMjDegreePrint` still assumed. The
[autofold spec](../../scratch/cmj-bridges/autofold.json) and
[preview output](../../scratch/cmj-bridges/autofold-output.txt) are conditional:
the generated proof names a future `cmPeriodJDescends_proof` that does not exist.
The script ran with `--dry-run` only. The projected improvement cannot be claimed today.

| State (29 H rows) | Strict | Strictest |
|---|---:|---:|
| Base | 4 LEAF / 25 GLUE | 4 LEAF / 25 GLUE |
| After these commits | 4 LEAF / 25 GLUE | 4 LEAF / 25 GLUE |
| Preview once the comparison is proved | 5 LEAF / 24 GLUE | 5 LEAF / 24 GLUE |

## Known issues

No error was found in the manuscript lines used or in the supplied Fowler reading.
The Cox Theorem 11.1 locator in the old row remains **UNVERIFIED** as a standalone
citation for the order version. The supplied reading of Fowler p. 613 cites both
its reference [10, Theorem 11·1] and [10, Proposition 13·2]. This work uses Fowler's
printed equality rather than an independently checked Cox locator.

## Manuscript check

| TeX lines | Verdict | Step |
|---|---|---|
| L584–585, L586–587 | unverified | Step 1: the scheme curve over L should have its Weierstrass j over L; the coefficient formula works once a corresponding equation is given, but the scheme-to-model comparison is open in Lean. |
| L584–586 | gap filled | Step 2, geometric part: the complex pullback along σ is an elliptic curve with the same full geometric endomorphism order. The j-value of an already given equation commutes with σ. |
| L586–587 | unverified | Step 2, j comparison: the analytic j-value of a period of the actual curve must agree with the image of its algebraic j; the needed membership is `CMPeriodJDescends`. |
| L585–586 | gap filled | Step 3: the lattice multiplier order is `ℤ[aτ]` and the primitive discriminant equals the discriminant of the full order. |
| L586–587 | gap filled | Step 4: the class number in the degree equality is identified with the finite Picard cardinal of the order. |
| L579, L586–587 | OK | Step 5: once the j-value is in L, its generated subfield has degree at most `d = [L:ℚ]`, and the manuscript already has `d ≤ D`. |
