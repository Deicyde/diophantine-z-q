# CM period j descent

**Scoped stop.** The open comparison is `CMPeriodShortWeierstrassComparison`: short
Weierstrass coordinates over `L` on the actual curve must pull back along a
uniformization for the given period to the normalized lattice coordinates, up to
one nonzero scale. Once this is proved, the Lean reduction gives
`CMPeriodJDescends` and then the live `CMjDegree` row from `CMjDegreePrint` alone.
The comparison remains open. No leaf or fold was added.

## Sizing

**VERIFIED (source interfaces).** `PkgI3.AbVar` is a scheme, and `IsPeriodAt`
concerns a map into the complex points of that very scheme at `σ`.
`ZInQ.LeafPush2.IsUniformization` makes pullbacks of supplied regular functions
holomorphic. The stronger coordinate uniformization also gives local holomorphic
coordinates by regular functions and an openness clause. These local coordinates
do not supply two functions with controlled poles at the origin over `L`.
Mathlib's `WeierstrassCurve` supplies a coefficient invariant and both
base-change and variable-change formulas. The vendored `PeriodPair` theory
supplies the ℘/℘′ equation and its surjective parametrization of the complex
Weierstrass **points**. Its construction of a lattice for a complex Weierstrass
equation chooses a period pair for that equation; it does not compare with a
period of the given scheme.

**VERIFIED (library search).** The allowed tree has function-field Riemann–Roch,
a smooth proper curve bridge to Riemann–Roch over an algebraically closed
field, and projective coherent GAGA. The curve bridge supplies a divisor formula
with a genus parameter. The GAGA map theorem used for the endomorphism ring
takes two already constructed abelian varieties. No declaration was found that
constructs short Weierstrass coordinates over `L` on the given scheme and
identifies them along its actual period map.

**SPECULATIVE (size).** A proof of the remaining comparison would need a
genus-one calculation of the pole spaces at the identity, over `L` or
with a base-change and descent argument, construction of `x` and `y` and their
short cubic relation, and identification with ℘ and ℘′/2 by their pole
parts on the complex torus. This is a separate development even if it
reuses the existing GAGA or Riemann–Roch work. One route is to choose the two
functions from the pole spaces at orders 2 and 3, normalize to a short
equation over `L`, then subtract the corresponding elliptic functions after
matching their principal parts. The difference has no pole on the compact
torus and is constant; the coordinate normalization fixes these constants.
The open proposition needs only two sections and their pullbacks, without a
packaged projective Weierstrass scheme isomorphism. The fixed-field route
does not avoid the missing link: field automorphisms of `ℂ` fixing `σ`L``
act on the point functor but need not preserve holomorphic maps. Applying
one directly to a uniformization is not justified.

## The comparison and the reduction

For `P := PeriodPair.ofTau τ`, the pointwise
`HasShortWeierstrassComparison A σ τ s Φ` asks for regular sections `x` and `y`
on an open of `A/L`, constants `a, b ∈ L`, and `u ∈ ℂˣ`. The sections satisfy
`y² = x³ + ax + b` over `L`. For each `z` off the lattice of `P`, the
point `Φ (fun _ => s * z)` lies in the open and evaluates `x` and `y` to
`u² ℘ₚ(z)` and `u³ ℘′ₚ(z) / 2`. The quantified
`CMPeriodShortWeierstrassComparison` asks for this along a witness of
each given `IsPeriodAt` on the curves in the CM row. The factors `s`
and `u` record the scale of the period witness and the normalization
of the algebraic coordinates, respectively.

The reduction is on-the-spot glue (provenance (c)). The complex lattice equation
and the evaluated section equation agree at points with ℘-values 0 and 1.
Consequently `σ(a) = u⁴ P.weierstrassCurve.a₄` and
`σ(b) = u⁶ P.weierstrassCurve.a₆`. The lattice discriminant is nonzero,
so the algebraic equation is nonsingular. The resulting scaling is a
Weierstrass variable change, which preserves `j`. The invariant of the
equation over `L` therefore maps to `modularJ τ`.

**VERIFIED (Lean).** [JDescent.lean](../../ZInQKernel/Contrib/OneProof/JDescent.lean)
compiled with `lake env lean`. The [axiom audit](../../scratch/j-descent/axioms-output.txt)
shows only `propext`, `Classical.choice` and `Quot.sound` for all five theorems.

| Theorem in `HDec.CMBranch.CMjBridges` | Statement |
|---|---|
| `sectionEval_const` (private) | Evaluation at a complex point in the open, over `σ`, sends the constant section of `a ∈ L` to `σ a`. |
| `exists_weierstrassP_eq` (private) | Every complex number is the ℘-value of a point off the lattice of any `PeriodPair`. |
| `modularJ_mem_range_of_shortCoordinates` | `HasShortWeierstrassComparison A σ τ s Φ → modularJ τ ∈ Set.range σ`. |
| `cmPeriodJDescends_of_shortWeierstrassComparison` | `CMPeriodShortWeierstrassComparison → CMPeriodJDescends`. |
| `cmjDegree_of_print_of_shortWeierstrassComparison` | `CMPeriodShortWeierstrassComparison → CMjDegreePrint → CMjDegree`. |

## Counts

**VERIFIED (live headline).** The [discharge scan](../../scratch/j-descent/discharges-output.txt)
matches `OpenResearchLeaves66.cmjDegree`. The new theorem still assumes
`CMPeriodShortWeierstrassComparison` and `CMjDegreePrint`.

**VERIFIED (dry run).** The [spec](../../scratch/j-descent/autofold.json)
and [output](../../scratch/j-descent/autofold-output.txt) preview the change
after the comparison is proved. The named comparison provider in the spec
is a placeholder. The dry run generates text and counts classifications;
it does not check that the provider exists.

| State (29 H rows) | Strict | Strictest |
|---|---:|---:|
| Base | 4 LEAF / 25 GLUE | 4 LEAF / 25 GLUE |
| After this work | 4 LEAF / 25 GLUE | 4 LEAF / 25 GLUE |
| Conditional preview, after the comparison | 5 LEAF / 24 GLUE | 5 LEAF / 24 GLUE |

## Known issues

No error was found in the manuscript lines used or in the supplied reading
of Fowler §2·1, pp. 612–613 (**STANDARD**, exact locator from the reading).
The degree in Fowler is for the normalized modular `j`. The manuscript
uses the field membership of the algebraic invariant of `E/L` implicitly;
the open Lean comparison is needed to apply Fowler to this curve over this
field. The Cox locator on the old row remains **UNVERIFIED** independently;
this work uses Fowler's supplied reading.

## Manuscript check

| TeX lines | Verdict | Step |
|---|---|---|
| L583–585 | OK | The row starts with the elliptic curve over `L` furnished by the matrix unit step. The existing scheme is the object used in the comparison. |
| L585–586 | gap filled | The preceding period bridge identifies the primitive discriminant of an actual period with that of the full geometric order and lands in Fowler's singular-modulus predicate. |
| L586–587 | unverified | Applying Fowler to `j(E)` over this `L` still requires identifying the lattice coordinates with regular sections of the same curve over `L`. A proof of the named comparison gives the missing field membership. |
| L579, L586–587 | OK | The already proved field degree inequality gives `h(Δ) ≤ [L:ℚ] ≤ D` once the comparison and the printed degree equality are supplied. |
