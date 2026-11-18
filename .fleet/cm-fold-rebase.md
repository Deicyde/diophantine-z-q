# cm-fold-rebase (2026-11-17)

**Result: the CM-branch fold is regenerated and compiles on main's current top (67950e829, open76/TailZ83).**
`HDec.HSyn.sixContactMin_of_open77_cm (r : OpenResearchLeaves58CM) t l : ZInQ.SixContactMin`, where
`OpenResearchLeaves58CM` = main's `OpenResearchLeaves57` − `gonzalezRotgerThm512X6RCF` + `cmFibreSplit` (GLUE) +
`fowlerProp27` (printed), `cmjDegree`, `cmPotentialGood`, `cmHeight62` (consequence), all pending review. CoxProperLattice,
HeightAdditivityUpper and ReducedCMPeriod are proved. Deliverable `ZInQKernel/Contrib/OneProof/CMFoldRebase.lean`
(`sixContactMin_of_open76_cmfold r t l (c : CMInputs3)`); modules `CMFoldRebase/{Top3,R5GR9_1,R5GR9,Open77}.lean`.
Main merged by a merge commit (no rebase).

**Why it was regenerated**: main's bost-gr9 (TailZ80) copied the bundle chain into `HSyn.GR9`, so cm-branch2's
R5Prune route (which needs bostLowerBoundAnSS) could not be reused as it was. The new generators
(`scratch/cm-fold-rebase/gen/`) thread the CM inputs through the GR9 chain, dirty-scan it (954 dirty constants),
reuse cm-branch2's 107 `_r5` copies and add 84 new ones (namespace-aware renamer), then drop the GR field.

**Compiles** (VERIFIED): lake build EXIT 0, first try. #print axioms = propext, Classical.choice, Quot.sound.
The frozenTarget dry run `scratch/cm-fold-rebase/MainDryRun.lean` compiles with standard axioms. The closure scan
finds no González–Rotger constant, no R5ptProps and no NoCM base, and all 31 fields of the new bundle are read.
#discharges: 30 open, 315 discharge one (15 pre-existing reductions and 300 projection noise from the copied
structures); none comes from this task, as expected.

**Count (kinds.tsv rule, new leaves pending review = GLUE)**: H rows, strict 5 LEAF / 24 GLUE on 29 (main) →
**strict 5 LEAF / 28 GLUE on 33** (this fold). If fowlerProp27 is later rated LEAF: **6 / 27 on 33**. All new rows
are in the research bundle. The fold raises GLUE, so autofold.py needs `--allow-rise`. Spec:
`scratch/cm-fold-rebase/autofold.json` (hand fold, `replaces`). Kinds rows: `scratch/cm-fold-rebase/kinds-rows.tsv`.

**Remains**: integrator's fold (Main.lean as in MainDryRun, kinds rows, OPEN.md); `cmFibreSplit` is open GLUE
(A8 at a CM fibre without NoCM, the inherited Known issue); reviews of the 4 leaves. Only Fowler can become LEAF as
stated. Report: docs/research/cm-fold-rebase.md.
