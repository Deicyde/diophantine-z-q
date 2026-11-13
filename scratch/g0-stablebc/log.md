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
- TestComp.lean (scratch test, minimal copies of AbVar/GroupModel): `baseChangeCompIso` and
  `groupModelBaseChangeExists` compile (9.5s). Trick: pasting lemmas `exists_pbPaste`
  (equation eliminated by `subst`) and `exists_pbSquare` over arbitrary schemes, instantiated
  afterwards; final composition via explicit `@CategoryTheory.instIsMonHomComp ... he hc`
  (instance search cannot see through `AbVar.baseChange`; unification can).
- run2 (01:57): full StableBC.lean, 0 errors, no sorry, 17s. Axioms [propext, Classical.choice,
  Quot.sound] for stableHeightBaseChange_of_glue, baseChangeCompIso, groupModelBaseChangeExists,
  stableHeightBaseChange_of_modelHeightBaseChange.
  VERIFIED: StableHeightBaseChange ⇐ ModelHeightBaseChange (h5-neron glue H4a) alone.
  H4b (h5-neron's kernel-timeout item) is now proved.
- run3 (02:00): added `ModelHeightBaseChangeLE` (the `≤` half of H4a, strictly weaker) and
  `stableHeightBaseChange_of_modelHeightBaseChangeLE`; 0 errors, no sorry; all axioms standard.
