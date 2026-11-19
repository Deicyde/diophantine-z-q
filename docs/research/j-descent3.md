# The function field and rational identity place in CM period descent

**Scoped stop.** The generic stalk of the given dimension-one abelian
variety is now a Tau Ceti function field over its exact constant field, and
the local ring at the identity gives a place of degree one. The remaining
comparison at this step is `AbVarFunctionFieldGenusOne`: that very field has
Tau Ceti genus one. A checked theorem then gives the full positive dimension
ladder at the identity, including `dim L(2O) = 2` and `dim L(3O) = 3`, and
functions of exact orders −2 and −3 with no other poles. The short cubic and
its comparison with the specified period remain open. No row was discharged.

## Sizing

**VERIFIED (source and Lean).** The abelian variety's structure morphism
gives an integral scheme and a field structure on its generic stalk.
The smooth chart calculation in
[Contrib/Dim/SmoothStalk.lean](../../ZInQKernel/Contrib/Dim/SmoothStalk.lean)
shows that relative dimension agrees with the given dimension at a closed
point of each standard smooth chart. The vendored
`AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one`
and `AlgebraicCurve.IsCurveOver.exists_separating_transcendental` supply the
transcendental generator and finiteness for `TauCeti.IsFunctionField`.
For the place, the vendor first identifies the range of the identity stalk
with a valuation subring. Tau Ceti attaches its own place to that same
subring. Evaluation at the unit section induces a map on the residue
field fixing the ground field, so the residue field has degree one.
Specialization embeds the algebraic closure of the constants inside
the function field into this residue field, proving exact constants.

**VERIFIED (source).** The
[high degree formula](../../ZInQKernel/Contrib/TauCeti/FieldTheory/FunctionField/Consequences/HighDegree.lean)
uses the genus defined from pole spaces. The
[scheme Riemann–Roch theorem](../../ZInQKernel/Contrib/CloudB3W16Torsion/Vendor/AnthropicFLT/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed.lean)
produces a curve model of an algebraically closed fibre with unspecified
genus. Tau Ceti's Weierstrass genus calculation starts from a nonsingular
equation. Neither evaluates the divisor-theoretic genus of this generic
stalk over the number field. Tau Ceti's `degree_weilDifferentialDivisor`
already gives degree `2g − 2` for the divisor of a nonzero Weil differential.

**SPECULATIVE (size).** An invariant differential proof needs at least
two pieces: the group-law trivialization of the curve's relative cotangent
line, and a comparison between the regular local orders of its rational
differential and the orders of a Tau Ceti Weil differential. The latter
needs the correspondence in both directions between closed points and
places; the present proof only needs the place attached to the identity.
An alternative is the existing Tau Ceti Hurwitz formula applied to
multiplication by two: transport the finite étale
map of degree greater than one to an extension of its own generic stalk
and identify the corresponding local ramification indices as one at
every place. Both routes need a separate scheme-to-function-field
development: at a minimum, centering places and matching either local
differential orders or ramification indices. The stop is at the genus
equality, without adding a hypothesis about a Weierstrass equation or
its period.

**SPECULATIVE (downstream plan).** Once the genus is proved, powers and
products with pole orders 0, 2, 3, 4, 5 and 6 form a basis of `L(6O)`.
Expressing `y²` in this basis gives a relation whose `x³` coefficient
is nonzero. Rescale, complete the square and translate `x` to get a
short cubic. If it has a multiple root `r`, then `r` lies in the base
field in characteristic zero and `y/(x-r)` would have a single simple
pole, contradicting `dim L(O) = 1`. Realize the normalized functions as
regular sections off the identity and establish evenness under inversion.
For the pole, use a uniformizer `t` and the unit numerator `t²x`. The
existing period witness gives holomorphy of regular evaluations. The
missing analytic check is that the evaluation of `t` on that witness
has nonzero derivative at zero. Then
`hasDoublePoleAtZero_of_localParameter` gives the required pole, and
`cmjDegree_of_print_of_doublePole` reduces the row to Fowler's statement.

## Lean statements

The names are in `HDec.CMBranch.CMjBridges`. They are on-the-spot glue
(provenance (c)). Here `K(A)` means `AbVarFunctionField A`, the actual
generic stalk with its structural algebra map.

| Theorem | Statement |
|---|---|
| `abVar_isIntegral` | The underlying scheme of a `PkgI3.AbVar L` is integral. |
| `abVar_smoothRelDimOne` | If `A.dim = 1`, the structure morphism of `A` is smooth of relative dimension one. |
| `abVar_isFunctionField` | In characteristic zero, if `A.dim = 1`, then `TauCeti.IsFunctionField L K(A)`. |
| `abVarIdentity_isClosed` | The image of the unit section is a closed point of the underlying scheme. |
| `degree_eq_one_of_section_stalk` (private) | For an integral scheme over a field, a place of the structurally induced function field whose valuation subring is the range of the stalk at a rational section has degree one. |
| `abVar_exists_identityPlace` | In characteristic zero, if `A.dim = 1`, there is a Tau Ceti place of degree one with valuation ring equal to the image of the identity stalk in `K(A)`. |
| `isIntegrallyClosedIn_of_rationalPlace` (private) | If a field extension has a Tau Ceti place of degree one, its base field is integrally closed in it. |
| `abVar_exactConstants` | In characteristic zero, if `A.dim = 1`, then `IsIntegrallyClosedIn L K(A)`. |
| `abVar_identityPoleSpaces_of_genusOne` | Given `AbVarFunctionFieldGenusOne`, every dimension-one `A` over a number field has a degree-one identity place with the above stalk comparison, `dim L(nO) = n` for every positive `n`, and for each `n ≥ 2) a nonzero function of order `−n` there and nonnegative order elsewhere. |

The unmatched proposition is
`AbVarFunctionFieldGenusOne := ∀ (L : Type) [Field L] [NumberField L]
(A : PkgI3.AbVar L), A.dim = 1 → TauCeti.genus L (AbVarFunctionField A) = 1`.

**VERIFIED (Lean).**
[JDescent3FunctionField.lean](../../ZInQKernel/Contrib/OneProof/JDescent3FunctionField.lean)
compiles under the Lake environment. The
[axiom audit](../../scratch/j-descent3/axioms-output.txt)
reports only `propext`, `Classical.choice`, and `Quot.sound` for every
new theorem. The [row-only discharge scan](../../scratch/j-descent3/discharges-output.txt)
uses the type of the live `OpenResearchLeaves66.cmjDegree` field; the full
entry point's import closure is outside this task's allowed imports.
The scan still reports both `CMPeriodShortCoordinatesDoublePole` and
`CMjDegreePrint` as premises of `cmjDegree_of_print_of_doublePole`.

## Counts

| H rows on the pinned base | Strict | Strictest |
|---|---:|---:|
| Before (29 rows) | 4 LEAF / 25 GLUE | 4 LEAF / 25 GLUE |
| After (29 rows) | 4 LEAF / 25 GLUE | 4 LEAF / 25 GLUE |
| Conditional preview with the coordinate comparison proved | 5 LEAF / 24 GLUE | 5 LEAF / 24 GLUE |

**VERIFIED (dry run).** The carried-forward [spec](../../scratch/j-descent3/autofold.json)
and [output excerpt](../../scratch/j-descent3/autofold-output.txt) use the
existing Fowler statement and the still-missing coordinate provider as a
placeholder. No fold was applied.

## Known issues

No error was found in the manuscript steps used or in the supplied reading
of Fowler §2·1, pp. 612–613 (**STANDARD**, exact locator from that reading).
The manuscript uses the algebraic `j(E)` of an elliptic curve over its
field of definition. The Fowler statement supplied here concerns the
modular `j` of the specified period. Identifying these values is implicit
in the manuscript. It is the open Lean glue; the new function-field results
alone do not identify them.

## Manuscript check

| TeX lines | Verdict | Step |
|---|---|---|
| L579 | OK | `d` is the degree of the same field `L` of definition used in the bound. |
| L583–585 | unverified | The matrix-unit and isogeny construction is upstream; this task takes the dimension-one curve over `L` as input. |
| L585–586 | gap filled | The earlier period-discriminant bridge identifies the primitive discriminant of the period with that of the full geometric endomorphism order. |
| L586–587 | unverified | The supplied Fowler reading gives the degree for the modular invariant. The genus comparison, the short coordinates and the analytic pole are still needed to apply it to the specified curve and period in Lean. |
| L587 | OK | Once the modular invariant is the image of an element of `L`, its generated subfield has degree at most `[L:ℚ] ≤ D`. |
