# Genus one on the CM degree path

**VERIFIED (Lean).** `HDec.CMBranch.CMjBridges.abVarFunctionFieldGenusOne`
proves `AbVarFunctionFieldGenusOne` for the actual generic stalk of any
dimension-one `PkgI3.AbVar` over a number field. The proof centers the
places on the curve, proves that doubling has ramification index one
everywhere and field degree four, and applies Tau Ceti's Hurwitz formula.
The unconditional `abVar_identityPoleSpaces` theorem gives
`dim L(nO) = n` for every positive `n` and functions with exact pole
orders two and three at the identity and no other poles.

The three new contribution modules and the row-only discharge scan
compile with `lake env lean`. All 16 theorem audits list only
`propext`, `Classical.choice` and `Quot.sound`. The
[report](../docs/research/j-descent4.md) and
[results log](../scratch/j-descent4/log.md) give the details. No source
error was found in the steps used.

**Effect at fold time: no change by itself**, strict or strictest.
`CMPeriodShortCoordinatesDoublePole` still needs the short cubic and the
comparison with the specified period, including the double pole. Once
that comparison is proved, one GLUE can be removed in both modes on main
with Fowler's statement already separated. No fold was applied.
