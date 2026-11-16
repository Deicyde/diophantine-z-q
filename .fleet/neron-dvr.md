# neron-dvr (gap-triage A8): final

**Proved (compiled, axioms [propext, Classical.choice, Quot.sound]).** File:
`ZInQKernel/Contrib/OneProof/NeronDVR.lean` (imports `ZInQKernel.Contrib.OneProof.BLRLocalizes` only; `lake build`
succeeds).

- `def GapNeron.NeronSchemeModelExistsDVRNF : Prop`: the field `ReductSplit.NeronSchemeModelExistsDVR` (TailZ7
  L238) verbatim, with `[NumberField K]` added.
- `theorem GapNeron.neronSchemeModelExistsDVRNF_of_field (h : ReductSplit.NeronSchemeModelExistsDVR) :
  NeronSchemeModelExistsDVRNF`.
- `theorem GapNeron.neronSchemeModelExistsNF (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists) :
  NeronSchemeModelExistsDVRNF`. N1 is the only hypothesis: `hB` was dropped, because gt-blr's
  `GapBLR.neronLocalizesDVR_proved` has no hypotheses. A variant `neronSchemeModelExistsNF'` keeps the A8
  signature, with `hB` unused.
- Restated consumers, each with `hN` at number fields:
  - SS1/SS3: `ss1_ss3_of_cpNF`, `ss1_ss3_of_cp_fullNF`, `semistable{Persists,ReductionThm}_{final,of_leaves}_nfNF`.
  - r6 and r8: `raynaudCriterion_leavesNF : … → RaynaudCriterionNF` and
    `grothendieckMonodromy_final'NF : … → GrothendieckMonodromyNF`. These conclude only the number-field
    restrictions of r6 and r8.
  - Combined: `r6_r8_NF_of_N1`.

**#discharges**: `66 open hypotheses, 1228 theorems checked, 3 discharge one`. The 3 are pre-existing
contributions; no `GapNeron` theorem matches, as expected, since the NF form is weaker than the field. No autofold
spec.

**Fold: the field cannot be dropped yet.** The consumer closure of `frozenTarget` was computed with a metaprogram
(`scratch/neron-dvr/Reach.lean`). The field has three real uses, all in TailZ23 at base 3782dac8e:

- **SS1/SS3, L763.** Reroutable: replace with `GapNeron.ss1_ss3_of_cpNF … (GapNeron.neronSchemeModelExistsNF
  t.neronSchemeExtensionExists) …`. Checked, compiles.
- **r6, L781.** `OpenResearchLeaves9.r6 : PkgI2.RaynaudCriterion` covers every field.
- **L803, read at TailZ9 L100 as r8.** `OpenResearchLeaves8.r8 : PkgI2.GrothendieckMonodromy` covers every field.

What the closure shows about r6 and r8:

- r8 is dead: no consumer reads it beyond copying it between bundles.
- r6 is applied only at number fields: at LPrefix L833 (through TailC `good_of_QML3` and TailF `qmModelG3_of`) and at
  TailH L2659.

So dropping the field needs new copies of the old generations `OpenResearchLeaves9..2` and `ResearchLeaves3`, with
r6 and r8 restricted to number fields and about 25 r6 consumers restated. That is the lead's chain-wide call.
docs/research/neron-dvr.md §3 has the full list.

**Remains (unchecked):**

- the chain-wide NF restatement of r6/r8 and its consumers;
- the general-DVR field itself (non-number-field `K`), which this task does not cover.

Coordination: the `semistableNeronBaseChange_of_printed*` theorems (gt-sga7) are not touched or needed.
