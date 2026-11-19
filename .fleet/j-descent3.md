# CM period descent: scoped stop at genus one

The function field bridge is proved through the rational identity place.
`ZInQKernel/Contrib/OneProof/JDescent3FunctionField.lean` uses the generic
stalk of the given dimension-one abelian variety. The ground field is its
exact constant field, and the identity place has degree one with valuation
ring equal to the image of the identity stalk. The module compiles; its
nine theorems use only the three standard axioms.

The first open comparison is
`HDec.CMBranch.CMjBridges.AbVarFunctionFieldGenusOne`. It asks for the
Tau Ceti genus of this generic stalk. This needs either a comparison of
invariant differentials with Weil differential orders or the ramification
comparison for an étale self-isogeny. Supplying it gives the positive
pole-space dimension ladder and functions with exact poles of orders two
and three at the identity, by a theorem already checked in Lean. The
construction of the short cubic and the nonzero derivative of a
uniformizer along the given period remain.

The row-only scan still requires
`CMPeriodShortCoordinatesDoublePole` to derive `cmjDegree` from Fowler.
Both actual counts remain 4 LEAF / 25 GLUE. The conditional dry run gives
5 LEAF / 24 GLUE in both counts. No fold was applied. See
`docs/research/j-descent3.md` for the statement and the manuscript check.
