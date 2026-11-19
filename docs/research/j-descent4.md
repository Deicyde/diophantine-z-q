# Genus of the abelian function field on the CM degree path

**VERIFIED (Lean).** For a dimension-one `PkgI3.AbVar A` over a number field `K`,
`HDec.CMBranch.CMjBridges.abVarFunctionFieldGenusOne` has type
`AbVarFunctionFieldGenusOne`: Tau Ceti's genus of the actual generic
stalk `K(A)` is one. The resulting identity place has
`dim L(nO) = n` for all positive `n` and functions with exact pole
orders two and three and no other poles. This step alone discharges no
row. The proofs are in
[JDescent4Places.lean](../../ZInQKernel/Contrib/OneProof/JDescent4Places.lean),
[JDescent4Degree.lean](../../ZInQKernel/Contrib/OneProof/JDescent4Degree.lean),
and [JDescent4Genus.lean](../../ZInQKernel/Contrib/OneProof/JDescent4Genus.lean).
All three compile with `lake env lean`. The
[axiom audit](../../scratch/j-descent4/axioms-output.txt) reports only
`propext`, `Classical.choice` and `Quot.sound` for every new theorem.

## Sizing and route

**VERIFIED (source).** The [sizing log](../../scratch/j-descent4/log.md)
records the comparison before the first build. Mathlib has the smooth
charts and local unramified ring results. The vendored curve library
uses `AlgebraicCurve.IsCurveOver` to obtain a separating parameter and
uses the proper valuative criterion to identify valuation rings with
stalks. The preceding contribution identifies the actual generic stalk
as a Tau Ceti function field over its exact constants and constructs the
rational place at the identity. The existing group object on
`PkgI3.AbVar` gives a doubling map; the torsion library proves it finite
étale and calculates its rank over an algebraically closed field.

The invariant differential route has a group law trivialization of
relative differentials in `CloudB3W16Cartier/GroupDifferentials.lean`
and comparisons of the corresponding stalks. Tau Ceti's
`degree_weilDifferentialDivisor` gives degree `2g-2`, but its
differentials are functionals on repartitions. An identification with the
scheme differential preserving orders at each place would still be needed.

The étale route instead uses ring maps already present. Properness
centers a normalized Tau Ceti place at a closed point. The target closed
point of a finite map gives the restricted place: its valuation ring maps
into the source valuation ring. The square of stalk maps and generic
stalk maps identifies these maps on elements. Formal unramifiedness
extends the target maximal ideal to the source maximal ideal, so a
uniformizer remains a uniformizer and the normalized index is one.

The generic fibre of a finite étale dominant map is the spectrum of the
source generic stalk. This compares the field degree with the finite
flat rank, which is locally constant and unchanged by base change.
Over an algebraic closure, the vendored degree calculation gives rank
four for doubling. Characteristic-zero tameness and index one give zero
different. The checked Hurwitz identity is then `2g - 2 = 4(2g - 2)`.
This uses no comparison with a scheme cohomological genus. The steps
are on-the-spot glue, provenance (c).

## Lean statements

Names are in `HDec.CMBranch.CMjBridges`; `K(A)` abbreviates
`AbVarFunctionField A`, with its structural constants map.
The field extension in the degree and ramification statements uses
the indicated scheme pullback as its scalar map.

| Declaration | Statement |
|---|---|
| `abVar_exists_placeCenter` | For a dimension-one abelian variety, each Tau Ceti place of `K(A)/K` has a closed point whose stalk image in `K(A)` is its valuation ring. |
| `abVar_exists_placeOf_closedPoint` | In characteristic zero, each closed point of such a curve gives a Tau Ceti place with this stalk image. |
| `stalk_functionField_square` (private) | For a dominant morphism of integral schemes, pulling a stalk element into the source generic stalk agrees with first pulling it into the source stalk. |
| `abVar_functionFieldMap_isScalarTower` | A dominant morphism over `K` induces an extension of function fields compatible with the two structural constants maps. |
| `abVar_ramificationIdx_eq_one_of_finite_unramified` | For a finite, dominant, formally unramified morphism over a characteristic-zero field between dimension-one abelian varieties, every Tau Ceti place of the source has index one over the target. |
| `genericFiber_isPullback` | For a dominant finite étale map of integral schemes, the square made by the generic stalk spectra and the associated map of schemes is a pullback. |
| `genericFiber_finite_finrank` | For such a map, the generic field extension is finite and its degree is the finite flat rank at the target generic point. |
| `abVarDouble_etale`, `abVarDouble_finite`, `abVarDouble_dominant`, `abVarDouble_over` | Doubling on an abelian variety is étale, finite and dominant in characteristic zero. In any characteristic it is a morphism over the ground field. |
| `double_baseChange_pullback` (private) | The comparison square of doubling before and after any extension of the ground field is a pullback. |
| `abVarDouble_finrank_of_isAlgClosed` (private) | In characteristic zero over an algebraically closed field, doubling has rank four at every point of a dimension-one abelian variety. |
| `abVarDouble_functionField_degree` | In characteristic zero, the self-extension of the generic stalk of a dimension-one abelian variety defined by pullback along doubling is finite of degree four. |
| `abVarFunctionFieldGenusOne` | The genus of `K(A)/K` is one if `K` is a number field and `A.dim = 1`. |
| `abVar_identityPoleSpaces` | For this curve the rational identity place has its identity stalk as valuation ring, every positive pole space has dimension `n`, and for every `n ≥ 2` there is a nonzero function of order `-n` there and nonnegative order elsewhere. |

## Counts and remaining work

The effect on main at fold time is **no change by itself** in either strict
or strictest mode. **VERIFIED (pinned base only):** the
[dry run](../../scratch/j-descent4/autofold-output.txt) shows 4 LEAF / 25 GLUE
before and after in both modes. The inherited
[conditional preview](../../scratch/j-descent4/autofold-conditional.json)
still has a placeholder for `CMPeriodShortCoordinatesDoublePole`. Its
[dry-run output](../../scratch/j-descent4/autofold-conditional-output.txt)
shows how the pinned base would reclassify the combined `cmjDegree` row
once that provider is available. With Fowler's statement already separated
on main, proving the coordinate comparison removes one GLUE in both modes.
The genus calculation adds no literature row, and neither dry run applies a
fold.

**VERIFIED (Lean).** The row-only [discharge scan](../../scratch/j-descent4/discharges-output.txt)
uses the live type of `OpenResearchLeaves66.cmjDegree` on the pinned base.
Its most reduced provider, `cmjDegree_of_print_of_doublePole`, still lists
`CMPeriodShortCoordinatesDoublePole` and `CMjDegreePrint` as premises on
that base.

The two functions supplied by the pole theorem still need to be
normalized to a nonsingular short cubic and matched to the specified
period. In particular, the algebraic coordinate used in the comparison
must have the required double pole in the actual period parameter.
Only then can the modular value in `CMjDegreePrint` be identified with
the algebraic invariant of the given curve. Fowler §2·1, p. 613 concerns
the degree of the singular modulus.

## Known issues

No source error was found in the manuscript steps used or in the
supplied Fowler reading. The remaining issue is a formal comparison:
the manuscript writes the algebraic `j(E)`, while Fowler's degree
statement concerns the modular invariant of the indicated period.

## Manuscript check

| TeX lines | Verdict | Step |
|---|---|---|
| L579 | OK | The degree bound uses the same field of definition `L` as the CM argument. |
| L583–585 | unverified | The matrix-unit and isogeny construction is upstream. This contribution takes the dimension-one abelian variety over `L` as input. |
| L584, L586–587 | gap filled | For the curve called elliptic here, the actual generic stalk has genus one and the rational identity has the indicated pole spaces. |
| L585–586 | OK | The discriminant in this step is that of the full geometric endomorphism order. The earlier discriminant comparison handles its identification with the period discriminant. |
| L586–587 | unverified | The supplied Fowler reading verifies the degree formula for the modular invariant. Genus one and the positive pole spaces establish the first part of the formal comparison with the curve; the short cubic and the period comparison remain. |
| L587 | OK | After descent of the specified value to `L`, its degree is at most `[L:ℚ] ≤ D`. |
