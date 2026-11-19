# CM degree descent after genus one

**Verified.** `HDec.CMBranch.CMjBridges.cmPeriodShortCoordinatesDoublePole_of_genusOne`
proves the coordinate comparison from `AbVarFunctionFieldGenusOne`.
`HDec.CMBranch.CMjBridges.cmjDegree_of_print_of_genusOne` gives
`CMjDegree` from that genus comparison and the existing Fowler statement,
`CMjDegreePrint`.

The proof constructs the nonsingular short cubic in the actual generic
stalk, realizes its coordinates on the complement of the identity, and
proves their inversion identities. It checks the exact double pole on the
specified period. Doubling acts to first order as $t\mapsto 2t$ in the
identity stalk; comparing the first nonzero term of the evaluated parameter
with its complex double gives order one. This leaves no derivative
comparison to supply.

All new Lean modules and the row-only `#discharges` scan compile. The
axiom audit lists only `propext`, `Classical.choice` and `Quot.sound`.
The genus proof remains a separate contribution. No fold was applied.
There is no count change from this contribution alone; with the genus and
coordinate comparisons both proved, strict and strictest GLUE each
decrease by one if the row is still live at fold time.

See `docs/research/j-descent5.md` and the verification in
`scratch/j-descent5/`. No source error was found in the steps checked.
