# sga735-finish (fleet note)

**Done: both pending readings of `sga7_IX_3_5_ForwardGeom` are removed, with −1 GLUE and no new GLUE.**
On 29 H fields, strict and strictest go from 11 LEAF / 18 GLUE to 12 / 17, using `scratch/sga735-finish/kinds-row-proposed.tsv`.

* **New leaf `SGA735Nil.SGA7_IX_3_5_ForwardUnipAC`, rated LEAF/LEAF (restricted printed form).** It is the field
  with two changes:
  * `[IsAlgClosed k(s)]` is added. This is sga735-narrow's step, and it removes reading (a), the `k(s)` reading.
  * The conclusion `(σ-1)² = 0` is weakened to `IsNilpotent (σ - 1)` on `T_ℓ`. This removes reading (b), the
    echelon clause.

  What is left is SGA 7 IX 3.5 "semistable ⇒ unipotent", which the print states under every recorded reading. It is
  compiled as a specialization of the old field.
* **What the consumer needs.** The live readers of r6's square-zero conclusion are `raynaudPlace_of_R6` (wild σ with
  a p-power period) and the ℓ = 3 QM consumer `goodReduction_of_QM_rational3_of_alg` (via `quatUnipotentTrivial`).
  Both need only that `σ - 1` is nilpotent on `A[ℓⁿ]` with one exponent for all levels.
* **Short path, with no new valuation algebra.**
  * Wild case: a downward induction that uses the old square-zero core.
  * QM case: `quatUnipotentTrivial` is applied to `1 + (S-1)^{2^i}` to halve the exponent.
* **What compiles, with standard axioms:**
  * `ZInQKernel/Contrib/OneProof/SGA7IX35Unip.lean`: the leaf, `SemistableUnipotentNilCP`, and
    `RaynaudCriterionNFNil` proved from the old hypotheses.
  * `SGA7IX35UnipReaders.lean`: `raynaudPlace_of_R6Nil` (same `RaynaudPlace` type),
    `goodReduction_of_QM_rational3_of_alg_nil`, and `nilQuat_trivial`.
  * The bypass fold `scratch/sga735-finish/FoldCheck.lean`. It is generated and copies 127 declarations with r6
    re-typed. `sixContactMin_of_open49 (r : OpenResearchLeaves32) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves25)`
    compiles with 0 errors. Its closure is free of the old field, `SemistableUnipotent` and `RaynaudCriterionNF`.
* **Kit outputs.**
  * `#discharges` has no line from the new files, as expected for a weaker leaf.
  * `Statement.lean` checks the copy by `rfl`.
  * `autofold.json` records a BYPASS spec.
* **Integrator.**
  1. Copy `FoldCheck.lean` to TailZ56 (325 KB, so split it if needed), or regenerate it with `R6Taint.lean` + `gen.py`.
  2. Switch Main to `sixContactMin_of_open49`.
  3. Replace the kinds row.

  This supersedes sga735-narrow's fold.
* **What remains.** The locator of 3.5 is still UNVERIFIED (nobody has read the display). The generator's copylib now
  copies `attribute [-instance]` context. Without it, the TailH copies hit typeclass timeouts.

Report: docs/research/sga735-finish.md.
