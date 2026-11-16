# pi0-fold: summary

Base ec797e65 (leaf-fold30). Report: docs/research/pi0-fold.md. Log: scratch/pi0-fold/log.md.

**The base did not build.** leaf-fold30's autofold wrote its persists-dvr top module over rigid-prune's `TailZ40`, and
TailZ23 imports TailZ40, so the build has a cycle.
* Fix, in its own commit 4a034cb1: rigid-prune's module is restored as `TailZ40`, leaf-fold30's module moves verbatim
  to `TailZ60`, and Main.lean imports `TailZ60`.
* The integrator must carry this fix (or an equivalent rename).

**Result (VERIFIED, compiled).** `frozenTarget` loses `OpenAddedLeaves17.deligneComponentsX6PrintedAb` and
`OpenAddedLeaves17.geomConnOfAlgClosure`, and gains nothing. The fold is in place, prune-style; no bypass was pasted.
* **Counts.** H fields go from 48 to 46. Strict kinds.tsv goes from 40 LEAF / 8 GLUE to 38 / 8, and strictest from
  39/9 to 37/9.
* **Build and axioms.** `lake build +ZInQKernel.OneProof.Main` succeeds. frozenTarget's axioms are propext,
  Classical.choice and Quot.sound.
* **PruneScan.** 0 unused fields out of 46.

**How.**
* The chain now carries the weak row `LeafAdopt.R1R2fpRepW` (`R1R2fpRep` without `R1pi0Props`, LPrefix).
  * 33 binders and internal-bundle fields are switched, and `R1R2fp_of_rep` is stated on the weak row.
  * Producers keep their strong conclusions.
* `x6Rows_of_open14` is built from pi0-prune's weak producers, pasted into TailZ21 (`x6Rows_of_leavesW`, with the base
  witness from `GonzalezRotgerX6`).
* Two Contrib files cannot be edited and both still compile unchanged:
  * sgr-fold's `SGRFold` works because `R1R2fp_of_rep` and `x6Rows_of_open14` switched together.
  * For st-qbar's `STQM`, the new contributor file `Contrib/OneProof/Pi0FoldSTQM.lean` restates
    `cm_point`/`stQM_of` on the weak row, and TailX uses `stQM_ofW`. `LeafQCheck.cmDescends_of` keeps its strong form
    by delegating to the new `cmDescends_ofW`.
* The prune then removes the 12 field copies (`OpenAddedLeaves12`–`17`), their 10 assignments, and 4 dead off-chain
  readers in TailZ22.

**Checks.**
* **DumpCompact/cmp_hashes.**
  * Removed: 16 constants, the 12 projections and the 4 dead readers.
  * New: 38 constants, all helpers.
  * Changed: 157 constants, of which 110 are generated auxiliaries of 18 edited structures and 47 are edited
    consumers or conversions, plus SGRFold's dependent term.
  * frozenTarget and every `sixContactMin_of_open*` keep their hashes.
* **DischargesTest.** The controls behave as before: t1 discharges `nvLocalInertia`, t2 discharges nothing, t3 is
  flagged for `sorry`.
* **Regenerated docs.** `OpenStatements.lean` and `render_open.py` regenerated the docs, and `render_open.py --check`
  passes.
  * render_open needed 4 stale claims.tsv rows deleted first (`igusaGL2`, `h29`, `elkiesX6StarPrinted`,
    `semistablePersistsSHcp`). Earlier folds had removed those fields, and the base fails the same way.

**Remains.** Trimming the now off-closure strong producers is optional. The §0 base fix has to reach the integration
branch.
