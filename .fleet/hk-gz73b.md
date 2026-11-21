# Gross–Zagier p. 310 handoff

**Verdict.** `hkConsumed_of_gz73` proves `HKConsumed` from the p. 310 form
of Gross–Zagier (7.3)(1) and the existing BCDT newform route. The theorem
uses the matching newform at its existential level, removing
`PoleNewformLevelIsConductor` with no new project GLUE. Fold after
Theorem 5.3. The existing Milne locator gap at L1784/L1788 and the stronger
modularity premise of the preprint cited at L1093 remain relevant to their
original uses.

**VERIFIED (Lean).** `HKGZ73.Reduction` and the scratch substitution into
`poleCompleteness_of_hkConsumed` compile. The analytic-rank dictionaries and
least-level proof are retained. `GZ73Print` and all four theorems use only
`propext`, `Classical.choice` and `Quot.sound`.
[Axioms](../scratch/hk-gz73b/axioms.txt)

**Remaining.** The p. 310 citation follows the lead’s reading, with an
independent page check pending. The BCDT route still uses Shimura, Li,
Carayol and Faltings, including the two existing GLUE readings. A fold now
would take 31 open rows to 35. Sharing the existing Theorem 5.3 suppliers
makes the replacement of `hK` one-for-one. If that assembly retains
`Prints.kolyvagin`, its rank-one instance already supplies `hK`.
[Research report](../docs/research/hk-gz73b.md)
