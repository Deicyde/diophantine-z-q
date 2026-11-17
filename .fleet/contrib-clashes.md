# contrib-clashes (final)

**Result.** All 4368 modules of `ZInQKernel/Contrib/` now import in one Lean environment. This also holds together
with `ZInQKernel`, `OneProof.Main` and `OneProof.Discharges` (VERIFIED). `Contrib/AllContrib.lean` is regenerated to
import all of them (it was stale at 3047 modules, with no OneProof), and `lake build ZInQKernel.Contrib.AllContrib`
succeeds.

**Clashes before (main e1b31749).** The olean scan (`scratch/contrib-clashes/ClashScan.lean`) found 72 names
duplicated across 74 project-module pairs (`clashes-before.txt`):
- 66 between `HDecomp.Textbook.Different` and `Contrib.Different.Local`;
- 3 `ZInQ.GZWeil.*` (WeilJacobi and JacobiLambdaDeriv);
- 3 for a CloudW07 auto-named local instance;
- 1 each for HP23Proof and TYZGenusFold instances.

Under Lean 4.35's import rule (`subsumesInfo`), identical theorems are accepted. Only 6 duplicates are fatal: the
definitions in Different (`TDifferent.phiF`, …, `PkgI6.TraceContainsRamificationIdx`).
**After:** 0 fatal clashes, and 0 duplicated non-auxiliary names among project modules.

**Fixes** (Contrib only, no statement changed, no importer edited):
- Different/Local re-exports the canonical HDecomp copy; it was identical up to line breaks.
- WeilJacobi imports JacobiLambdaDeriv. Its own proof is kept as `jacobiLambdaDeriv_viaCuspForms`.
- Duplicate local instances are `private`: 2 OneProof files and 3 vendored CloudW07 files, with NOTICE and
  comment lines updated.

**Checks.**
- All 4368 Contrib modules build (0 errors).
- `frozenTarget`, `sixContactMin_of_open55` and all 542 `print_axioms` declarations use only the standard axioms.
- `#discharges`: the 49 discharge blocks are identical. Only the summary count changed, from 11113 to 11116
  theorems checked, because of 3 new non-discharging constants (explained in report §4).

**Remaining.** Nothing for this task. No hypothesis was discharged, so there is no OneProof theorem or
autofold spec. Report: docs/research/contrib-clashes.md. Log: scratch/contrib-clashes/log.md.
