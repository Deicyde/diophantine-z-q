# CM period comparison handoff

**Scoped stop.** The remaining glue is
`HDec.CMBranch.CMjBridges.CMPeriodShortCoordinatesDoublePole`.
On the given dimension-one abelian variety over its number field, supply
two regular sections satisfying a nonsingular short cubic and certify
that the pullback of the even coordinate `x` has a double pole at zero
on the given period. Tau Ceti already has the dimension formula for
`L(nP)` at a rational place of a genus-one function field. The missing
work is attaching that formula to the actual scheme and its identity,
constructing the sections over the number field, and checking a regular
parameter along the period witness. The local-parameter lemma reduces the
pole check to a nonzero derivative of the parameter and a nonzero
numerator after clearing the pole.

**VERIFIED.** [JDescent2Analytic.lean](../ZInQKernel/Contrib/OneProof/JDescent2Analytic.lean)
and [JDescent2.lean](../ZInQKernel/Contrib/OneProof/JDescent2.lean)
compile. The cubic and the single pole force both lattice coordinates
with one scale, without a pole premise for `y`. This gives the original
short Weierstrass comparison and period `j` descent conditional on the
named glue. The live scan matches `cmjDegree` from that glue and
`CMjDegreePrint`. All eight new theorems use only the three standard axioms.

Both actual counts remain 4 LEAF / 25 GLUE. The conditional dry run
gives 5 LEAF / 24 GLUE in both counts. No fold was applied. No error
was found in the manuscript lines used or the supplied Fowler reading.
See the [report](../docs/research/j-descent2.md) and
[verification files](../scratch/j-descent2/).
