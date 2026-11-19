# CM period j descent

**Scoped stop.** `CMPeriodJDescends` remains open. The coordinate uniformization
pulls back regular functions but does not construct the short Weierstrass
coordinates of the given scheme over its field of definition. The exact missing
glue is `CMPeriodShortWeierstrassComparison`: for the given CM period, find two
regular sections over `L` satisfying a short cubic and evaluating along that
period map to the lattice's ℘ and ℘′/2 with weights 2 and 3 in a single scale.
This statement needs no packaged scheme isomorphism. Its proof still needs
the pole spaces at the identity over `L` and the matching of their normalized
coordinates with the complex uniformization. Existing coherent GAGA and
Riemann–Roch infrastructure may support that separate development.

**VERIFIED.** [JDescent.lean](../ZInQKernel/Contrib/OneProof/JDescent.lean)
compiles. The evaluated section equation determines both coefficients and shows
that the algebraic invariant over `L` maps to `modularJ τ`. The reduction
then gives `CMPeriodJDescends` and the live `cmjDegree` row, conditionally.
All five new theorems use only the standard axioms. The live discharge scan
lists both the comparison and `CMjDegreePrint` as premises.

Both actual counts remain 4 LEAF / 25 GLUE. The read-only preview reaches
5 LEAF / 24 GLUE after the comparison; its provider is a placeholder.
No fold was applied. No error was found in the manuscript lines used or
the supplied Fowler reading. See the [report](../docs/research/j-descent.md)
and [verification files](../scratch/j-descent/).
