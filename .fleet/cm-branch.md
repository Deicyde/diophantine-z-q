# cm-branch (2026-11-17): the manuscript's CM branch in Lean; H compiles without NoCM

**Verdict.** The CM paragraph of diophantine_zq.tex (L581-631) is formalized from the leaves it cites, the
case split is a Lean proof, and the chain's non-CM half is localized to fibres without CM. The fold dry run
`HDec.HSyn.sixContactMin_of_open67_cm (r t l) (c : CMBranch.CMInputs) : ZInQ.SixContactMin` compiles with
standard axioms; its constant closure contains no NoCM (FS5, `FS5NoCM.*`, `cmOptimalEmbedding`,
`x6ConicModel` all gone, nothing added). Target only partly met: `gonzalezRotgerThm512X6RCF` is still
carried as the unread conjunct `R5ptProps` of the moduli row `r1r2` (needs a weak-row prune), and
`x6CoarseModuliIdeal`, `elkiesX6StarEveryIdeal` also build the row's `X₆` and `π₆`, so they are not
NoCM-only and stay.

**What compiles (VERIFIED, `lake build`, axioms propext/Classical.choice/Quot.sound).** New files under
`ZInQKernel/Contrib/OneProof/`: `CMBranch/Arith.lean` (Eq. (6.2) over Mathlib's η and its expansion,
q-series bound, summand ≤ πy/6+1, ≤ B_cm), `CMBranch.lean` (leaves, glue, `cmOutput_of`,
`le_heightCcm_of_cmOutput`, `cmBranchOut_of`, `glueOutputs_of_branches`), `CMBranch/NonCM.lean`,
`CMBranch/Localize.lean` (`ModularConstituentNC` without FS5), `CMBranch/Open4.lean`, `CMBranch/Top.lean`.
`#discharges`: no field discharged (re-route). Fold: hand-fold spec `scratch/cm-branch/autofold.json`.

**New statements.** Leaves: `FowlerProp27` (printed, Fowler 2026 Prop. 2.7), `CMHeight62` (consequence of
BCCGM 2017 Eq. (6.2)), `CMjDegree`, `CMPotentialGood` (classical; uncited in the manuscript — Known issue).
Glue: `CMFibreSplit` (A8 for a CM fibre + matrix units), `ReducedCMPeriod` (on-the-spot),
`HeightAdditivityUpper`. Reused: `R19_GaudronRemond`, `R20Lower`.

**Remains.** (1) Run the hand fold (raises GLUE by 3, needs `--allow-rise`); (2) prune `R5ptProps` from
`R1R2fpRepW` (81 type-level consumers listed in `scratch/cm-branch/rowuse.txt`) to drop González–Rotger
5.12; (3) prove the three glue Props; (4) re-source R2 to `Y₃ → P¹_j` to drop the `X₆` fields.
Report: docs/research/cm-branch.md.
