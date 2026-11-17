# cm-branch (2026-11-17): the manuscript's CM branch in Lean; H compiles without NoCM and without González–Rotger 5.12

**Verdict.** The CM paragraph of diophantine_zq.tex (L581-631) is formalized from the leaves it cites, the
case split is a Lean proof, and the chain's non-CM half is localized to fibres without CM. Two compiled fold
dry runs (standard axioms):
* `HDec.HSyn.sixContactMin_of_open72_cm (r t l) (c : CMBranch.CMInputs)` — NoCM (FS5, `FS5NoCM.*`,
  `cmOptimalEmbedding`, `x6ConicModel`) gone from the closure;
* `HDec.HSyn.sixContactMin_of_open72_cm_no5 (r t l) (c)` — also prunes the row conjunct `R5ptProps`: of the
  top bundles' fields it reads all that the current top reads **except `gonzalezRotgerThm512X6RCF`**, and
  nothing new (`scratch/cm-branch/topfields.txt`).
`x6CoarseModuliIdeal`, `elkiesX6StarEveryIdeal` stay: they also build the moduli row's `X₆` and `π₆`
(not NoCM-only; the manuscript uses `Y₃ → P¹_j` instead — separate re-route).

**What compiles (VERIFIED, `lake build`).** New files under `ZInQKernel/Contrib/OneProof/`: `CMBranch/Arith.lean`
(Eq. (6.2) over Mathlib's η, its expansion, q-series bound, summand ≤ πy/6+1, ≤ B_cm), `CMBranch.lean`
(leaves, glue, `cmOutput_of`, `le_heightCcm_of_cmOutput`, `cmBranchOut_of`, `glueOutputs_of_branches`),
`CMBranch/NonCM.lean`, `CMBranch/Localize.lean` (`ModularConstituentNC` w/o FS5), `CMBranch/A8.lean`
(A8 for every fibre w/o NoCM), `CMBranch/Open4.lean`, `CMBranch/Top.lean`, `CMBranch/No5A…E.lean` (generated
prune). `#discharges`: none (re-route). Fold: hand-fold spec `scratch/cm-branch/autofold.json`.

**New statements.** Leaves: `FowlerProp27` (printed, Fowler 2026 Prop. 2.7), `CMHeight62` (consequence of
BCCGM 2017 Eq. (6.2)), `CMjDegree`, `CMPotentialGood` (classical; uncited in the manuscript — Known issue).
Glue: `CMHomFieldSplit` (matrix units on A8's model), `ReducedCMPeriod` (on-the-spot),
`HeightAdditivityUpper`. Reused: `R19_GaudronRemond`, `R20Lower`.

**Remains.** (1) Lead: do the fold in place (edits listed in docs/research/cm-branch.md §6; GLUE +3, needs
`--allow-rise`), then PruneScan; (2) prove the three glue Props; (3) re-source R2 to drop the `X₆` fields.
Report: docs/research/cm-branch.md.
