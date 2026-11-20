`ThetaClose.actualPmLocal` constructs the Appendix F local data on the
explicit level order. It supplies every good-prime indexed class, lattice,
and norm comparison, and chooses the level characters with their (O.3)
parity in the coefficient ring of the generated field. The filtered sphere
support is `ThetaClose.actualFilteredSupport`. The same local data feed
`actualLevelStage` and `actualLevelValLift`.

Two inherited issues are recorded in the research report. The frame
requires the integral-unit correction between the separately chosen local
generators. The inherited Lean support proposition puts the sphere
hypotheses on the left side of the equivalence; the new proposition
uses the manuscript's scope. The unfiltered support claim remains false.

All five Lean modules compile individually. The audit of 39 theorems
and 24 other declarations reports only `propext`, `Classical.choice`,
and `Quot.sound`. No new printed leaves are used.

The local constructor still takes the upstream discriminant, detecting
prime and level data, and the Atkin–Lehner signs. The stage and valuation
lift take the separately owned PM geometry, evaluation, and multiplier.
The orbit and character comparisons of (O.7) are downstream.

Verified result commit: `02a9d9684c30b124a5386fe95eafca870091c989`.
This handoff is the final commit on top of that result.
See `docs/research/rc-theta-close.md` for the exact statements and owners.
