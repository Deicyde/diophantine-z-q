# theta-fold2 (fleet summary)

**Result (VERIFIED):** `frozenTarget` loses `OpenAddedLeaves17.thetaRatiosAlgebraic` (composite, GLUE) and gains
nothing. kinds.tsv H count 45 → 44; strict 34 LEAF / 11 GLUE → 34 / 10 (strictest the same). Base 47aaf586
(leaf-fold31) builds.

**How:** done in place, without applying theta-direct's fold.patch. TailK cannot import theta-direct's proof, because
ThetaDirect's imports reach TailZ24. TailZ25 is outside that import set, so:
* `gluePieces_of_open4` takes `hθ : QMHauptmodul → ThetaRatiosAtQM`; theta-split's block moved from theta-direct's
  UseForm.lean into TailK, and UseForm.lean is deleted;
* `hθ` is threaded through `sixContactMin_of_open4`, `_open6`–`_open15`, `_open17` and `_open18`;
* TailZ25's `sixContactMin_of_open19` supplies `HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul`.

`_open19`–`_open35`, Main.lean, frozenTarget (hash and pp.all type unchanged) and the Contrib tops are untouched. After
that, the field was pruned from OpenAddedLeaves4, 6–9 and 12–17: 11 fields, 12 assignments and 1 constructor
element.

**Compiles / checks:**
* `lake build +ZInQKernel.OneProof.Main` succeeds (13706 jobs), and frozenTarget's axioms are
  `[propext, Classical.choice, Quot.sound]`.
* PruneScan finds 44 fields, 0 unused.
* DumpCompact/cmp_hashes: removed only the 11 projections; new only the ThetaDirect modules plus the 6 moved TailK
  declarations; changed only structure auxiliaries, conversions, `gluePieces_of_open4` and the `sixContactMin_of_open*`
  listed above.
* DischargesTest controls are as before, with 55 open hypotheses.
* docs/one-proof and STATUS.md were regenerated, and `--check` passes.

**Remains:** older off-closure bundles (GluePieces2/3, OpenAddedLeaves2/3/5/10/11, Q5–Q10) still carry the field.
They are not in the prune set, so they were left alone. Report: docs/research/theta-fold2.md.
