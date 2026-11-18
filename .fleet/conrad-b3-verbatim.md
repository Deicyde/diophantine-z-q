# conrad-b3-verbatim

C8 is reduced to one printed-form row, `ConradAppBPrint`. It pairs Conrad's
near-one formula at local base `ℚ_p` and the full-group tensor splitting from
Proposition B.3. The Lean proof derives the identity-line statement over its
stabilizer and proves that the old formula on Artin lifts agrees with the
printed formula on the abelianization. The original consumer is unchanged.

**VERIFIED:** merged main `c3624d0e3` in `bf5bfc05c`. The contribution,
verbatim statement copies, current `Main`, and the generated scratch fold
compile. `#discharges` matches `OpenAddedLeaves28.conradAppB` using only
`ConradAppBPrint`. The discharge and both top wrappers use just `propext`,
`Classical.choice`, and `Quot.sound`. Verification and report: `535c79d11`.

The manuscript at `sec:height` L755–767 needs the common weight at five to
match the cyclotomic exponent. The stabilizer form is proved Lean glue.
The [report](../docs/research/conrad-b3-verbatim.md) records the printed
clauses, sign, and application. No new page read was needed.

The [fold spec](../scratch/conrad-b3-verbatim/autofold.json) is ready and
was left unapplied. Conrad's printed results remain the assumption. H strict
LEAF/GLUE on N: 5/27 on 32 before, 6/26 on 32 after if the exact cited
preprint is eligible; 5/27 on 32 after if refereeing is required.
