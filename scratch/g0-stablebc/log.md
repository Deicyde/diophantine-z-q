# g0-stablebc log

- Merged origin/wip/g0-split (Split.lean, the piece) and origin/wip/h5-neron (glue H4a/H4b, compositum).
- `StableBC.lean` = `Defs.part` (Split.lean lines 16667-18351 verbatim: def-faltings objects through
  NeronSec, then the closing `end`s) + `Main.part` (the piece, verbatim; h5-neron's
  `IsBaseChangeOf`, `ModelHeightBaseChange`, `GroupModelBaseChangeExists`, `compositum` copied;
  new `BaseChangeCompIso`, `transportModel`, `transportMetrized`, `transportModel_height_le`,
  `stableHeightBaseChange_of_glue`).
- run1 (01:50): `lake env lean scratch/g0-stablebc/StableBC.lean`: 0 errors, no sorry, 2m43s.
  `#print axioms G0StableBC.stableHeightBaseChange_of_glue` = [propext, Classical.choice, Quot.sound].
  VERIFIED: StableHeightBaseChange ⇐ BaseChangeCompIso ∧ GroupModelBaseChangeExists ∧ ModelHeightBaseChange.
