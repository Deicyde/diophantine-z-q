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
- run4-6 (02:05-02:10): added the Arakelov half of H4a. Fixes: `η`, `ι` are tokens under
  `open MonObj` (renamed `w`, `ψ`); `mul_one` ambiguous (`_root_.mul_one`); FractionalIdeal set
  coercion (use `have e1' : … := e1` by defeq instead of `rw`).
  run6: 0 errors, no sorry, 40s. Axioms standard for `secIndex_baseChange`,
  `modelHeight_eq_of_isHodgeBaseChange`, `modelHeightBaseChangeLE_of_metrization`,
  `stableHeightBaseChange_of_metrization` (and all earlier theorems).
  VERIFIED: StableHeightBaseChange ⇐ MetrizationBaseChange (geometric glue, stated).
- Statement checks (VERIFIED by diff): `StableHeightBaseChange` docstring+body = Split.lean
  19484-19494; Defs.part body = Split.lean 16667-18351; h5-neron's three defs identical.
- Read-only model review (no Lean run) of BaseChangeCompIso, ModelHeightBaseChangeLE,
  IsHodgeBaseChange, MetrizationBaseChange: all TRUE, none vacuous; two docstring fixes applied
  ("strictly weaker" → "implied by"; verbatim docstring restored, note moved to a comment).
- `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` (6 s,
  builds upstream lean/ helpers) so that Split.lean's imports resolve.
- run7 StableBC.lean after docstring fixes: 0 errors, 9 axiom lines all standard, no sorryAx.
- run8 SplitPlus.lean (= Split.lean + Main.part + integration theorems): 0 errors, no sorry,
  2m47s. `G0StableBC.split_piece_iff : HSyn.G0Split.StableHeightBaseChange ↔
  G0StableBC.StableHeightBaseChange := Iff.rfl`; `G0StableBC.glueOutputs_of_leaves_metrization`
  (g0-split's main theorem with `hBC` replaced by `MetrizationBaseChange`): axioms
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- run9-10 (02:15): added `HodgeLineBaseChange` (geometric glue over group models only: natural
  map ψ on Hodge spaces, lattice, finrank, uniformization compatibility) and the proved
  `metrizationBaseChange_of_hodgeLine` (builds the Hodge data of 𝒢': coordinate e : L' ≃ V',
  τ'-semilinear extension of coeff) and `stableHeightBaseChange_of_hodgeLine`. Fix: `mul_assoc`
  ambiguous under `open MonObj`. 0 errors, no sorry, axioms standard (11 lines).
  VERIFIED: StableHeightBaseChange ⇐ HodgeLineBaseChange.
