# CM period comparison from a double pole

**Scoped stop.** The remaining glue is
`HDec.CMBranch.CMjBridges.CMPeriodShortCoordinatesDoublePole`. On the
given curve over `L`, supply two regular sections on an open containing the
nonidentity complex points. They must satisfy a nonsingular short cubic over
`L`, and the evaluated $x$-coordinate must be even with an exact double
pole at the origin of the given period. The Lean reduction recovers both
lattice coordinates with one scale. It needs no separate pole condition for
$y$, no comparison of two chosen periods, and no scheme isomorphism with a
Weierstrass model. The named glue remains unproved. Once supplied, the
reduction gives `CMPeriodShortWeierstrassComparison`, hence
`CMPeriodJDescends`, and the live degree row from `CMjDegreePrint` alone.

## Sizing

**VERIFIED (source).** Tau Ceti's
[`Divisor.dim_natCast_zsmul_ofPoint_of_genus_eq_one`](../../ZInQKernel/Contrib/TauCeti/FieldTheory/FunctionField/Consequences/HighDegree.lean)
gives `dim L(nP) = n * deg P` for a genus-one function field over its
exact constant field. Its
[Weierstrass function-field file](../../ZInQKernel/Contrib/TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Genus.lean)
computes the pole spaces and genus starting from a given nonsingular
Weierstrass equation. The
[vendored scheme-to-Riemann–Roch theorem](../../ZInQKernel/Contrib/CloudB3W16Torsion/Vendor/AnthropicFLT/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed.lean)
instead attaches a curve model and a divisor formula to a smooth proper
geometrically integral curve fibre over an algebraically closed field. Its
genus is unspecified. The Jacobian and curve modules were checked for a
bridge from the actual `PkgI3.AbVar L` to the first theorem with its identity
as the rational place. No such bridge was found.

**VERIFIED (source).** The projective coherent GAGA comparison
[`ComplexAnalytic.gaga₁`](../../ZInQKernel/Contrib/CloudB3W17bOka/Oka/Analytification/GAGA/ProjectiveGAGA.lean)
identifies cohomology for a supplied coherent sheaf on a supplied projective
complex scheme. It does not construct the sheaf of the identity divisor
of this curve over `L` or identify its analytic sections with pole-bounded
functions on this period plane. The regular-function clause of
`LeafPush2.IsUniformization` does suffice for holomorphy on the preimage
of the open. The stronger uniformization supplies local coordinates and
openness, but these coordinates are not the pole spaces and the clause
belongs to the stronger witness. The period statement uses the weaker
uniformization.

**SPECULATIVE (remaining size).** The shortest route identified is a separate
curve development: attach the rational identity place and its valuations
to the actual function field over `L`, show exact constants and genus one,
use the existing ladder at orders 1, 2, 3 and 6 to construct and normalize
the cubic, and turn the order of $x$ at the identity into a local
parameter computation on the specified period. The new local lemma reduces
the last step to evaluating a regular parameter $t$ and a regular
numerator $v=t^2x$ at the identity: check that $t(0)=0$,
$t'(0)\ne0$ and $v(0)\ne0$. Invariance of $x$ under inversion gives
the evenness condition. This route needs several scheme and function-field
interfaces; no projective coherent GAGA development or global comparison
of meromorphic functions is needed after this point.

## Lean reduction

Subtract the principal part of $x$ at zero using $\wp$. Evenness makes
the coefficient of the simple-pole term zero. The difference extends
across the lattice and is constant by periodicity and Liouville, so
$x=c\wp+d$ with $c\ne0$. Each root of the nonsingular short cubic can
be tested at a point where $x$ has that value, since $\wp$ reaches
every complex value. Differentiating the cubic at such a point forces
$\wp'=0$, because $y=0$ and the root is simple. Thus each root of the
monic cubic in $\wp$ is also a root of the lattice cubic. Both have
degree three, so they coincide. The quadratic coefficient gives $d=0$.
Choose $u$ with $u^2=c$. The two candidates for $y$ now have the
same square, and the analytic identity theorem on the complement of
the lattice fixes the sign everywhere. Replacing $u$ by $-u$ if
needed gives $x=u^2\wp$, $y=u^3\wp'/2$.

These proofs are on-the-spot glue (provenance (c)). The names below are
in `HDec.CMBranch.CMjBridges`.

| Theorem | Statement |
|---|---|
| `hasDoublePoleAtZero_of_localParameter` | If $t,v$ are analytic at zero, $t(0)=0$, $t'(0)\ne0$, $v(0)\ne0$, and $t^2 f=v$ near zero off zero, then $z^2 f(z)$ has an analytic extension with nonzero value at zero. |
| `affine_weierstrassP_of_even` (private) | An even lattice-periodic function, analytic off the lattice with an exact double pole at zero, is $c\wp+d$ off the lattice with $c\ne0$. |
| `exists_value_weierstrassP` (private) | Every complex value occurs as a $\wp$-value off the lattice. |
| `shortCubic_coordinates_of_doublePole` | Two functions analytic off the lattice on a nonsingular short cubic, with $x$ even and periodic and having an exact double pole at zero, equal $u^2\wp,u^3\wp'/2$ off the lattice for one nonzero $u$. |
| `modelEval_const` (private) | Evaluation of an $L$-constant section at a complex point over `σ` gives its image under `σ`. |
| `shortWeierstrassComparison_of_doublePole` | For the given scaled period witness, `HasShortCoordinatesWithDoublePole` implies `HasShortWeierstrassComparison` on that witness. |
| `cmPeriodShortWeierstrassComparison_of_doublePole` | `CMPeriodShortCoordinatesDoublePole → CMPeriodShortWeierstrassComparison`. |
| `cmjDegree_of_print_of_doublePole` | `CMPeriodShortCoordinatesDoublePole → CMjDegreePrint → CMjDegree`. |

**VERIFIED (Lean).** [JDescent2Analytic.lean](../../ZInQKernel/Contrib/OneProof/JDescent2Analytic.lean)
and [JDescent2.lean](../../ZInQKernel/Contrib/OneProof/JDescent2.lean) compile
under `lake env` with the exact base dependencies. All eight theorems have
only `propext`, `Classical.choice` and `Quot.sound` in the
[axiom audit](../../scratch/j-descent2/axioms-output.txt). The live
[discharge scan](../../scratch/j-descent2/discharges-output.txt) matches
`OpenResearchLeaves66.cmjDegree` and lists only the named glue and
`CMjDegreePrint` as premises of the new reduction.

## Counts

| H rows on the pinned base | Strict | Strictest |
|---|---:|---:|
| Before (29 rows) | 4 LEAF / 25 GLUE | 4 LEAF / 25 GLUE |
| After this work (29 rows) | 4 LEAF / 25 GLUE | 4 LEAF / 25 GLUE |
| Conditional preview after the remaining glue is proved | 5 LEAF / 24 GLUE | 5 LEAF / 24 GLUE |

**VERIFIED (read-only preview).** The [spec](../../scratch/j-descent2/autofold.json)
and [output](../../scratch/j-descent2/autofold-output.txt) preview replacing
`cmjDegree` with the already stated Fowler theorem. The proof name for
`CMPeriodShortCoordinatesDoublePole` is a placeholder in the dry run.
No fold was applied.

## Known issues

No error was found in the manuscript lines used or in the supplied reading
of Fowler §2·1, pp. 612–613 (**STANDARD**, exact locator from that reading).
Fowler's degree equality is for the modular invariant, while the degree
bound uses the field of definition of the curve; the comparison between
these two invariants is implicit in the manuscript. The Lean identification
of the full CM order with the order of the period and the field degree
inequality are already in the tree. The unresolved point is obtaining the
sections and certifying the double pole on the same curve and period.

## Manuscript check

| TeX lines | Verdict | Step |
|---|---|---|
| L579 | OK | The bound uses the degree of the same field $L$ over which $E$ is furnished. |
| L583–585 | unverified | The matrix-unit construction is upstream of this task. Here the elliptic curve over $L$ is the input. |
| L585–586 | gap filled | The existing period-discriminant bridge identifies the primitive period discriminant with that of the full geometric endomorphism order. |
| L586–587 | unverified | The degree equality follows from the supplied Fowler reading once the modular $j$ for this period is shown to be the image of an element of $L$. The analytic normalization is proved; producing its algebraic input remains open. |
| L587 | OK | Given this field membership and Fowler's equality, the degree of the generated subfield is at most $[L:\mathbb Q]\le D$. |
