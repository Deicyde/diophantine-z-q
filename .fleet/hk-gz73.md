# Gross–Zagier's rational-point implication for pole completeness

**Verdict: conditional proof; do not fold.** The manuscript's Milne locator
at L1784 does not by itself supply newness or the Hecke equivariance at
L1788. The old source at L1093 is an unrefereed preprint whose modularity
premise is stronger than the old Lean coefficient predicate. No
mathematical error was found in the checked pole steps.

**VERIFIED (Lean).** `hkConsumed_of_gz73` applies the Gross–Zagier print
draft to the pole curves using the existing BCDT adapter and newform
route. The matching newform's level equals `CST.newformLevel` in Lean.
The equivalence between analytic rank one and a zero central value with
nonzero derivative holds for any entire continuation and needs no GLUE.
The new file and scratch substitution into pole completeness compile.
All four new theorems have only `propext`, `Classical.choice` and
`Quot.sound`.

**Open.** `PoleNewformLevelIsConductor` is one new GLUE, comparing the
least matching modular level with the conductor of the actual
cohomological Tate representations. The existing newform route carries
two other GLUE readings, Carayol and Faltings. `GZ73Print` remains a draft
until the two-lens review checks the printed standing assumptions and
the conductor convention.

Before Theorem 5.3 is folded, the proposed change takes 31 rows to 36.
Even after sharing its newform suppliers, it adds one row and does not
lower GLUE. The current Theorem 5.3 assembly also retains its own
Kolyvagin input, whose rank-one instance already implies the old `hK`
type. No assembly or registry was changed. See
`docs/research/hk-gz73.md` for the manuscript audit and counts.
