# y3-x6 log

## 2026-11-17

- Read (VERIFIED): docs/research/y3-p1j.md, .fleet/y3-p1j.md, scratch/y3-p1j/log.md, docs/research/cm-branch2.md (§5 scope),
  scratch/cm-branch2/clauseuse.txt, CMBranch/R5Prune*.lean, CMBranch/Open73.lean.
- Base of this task = cm-branch2's route: top `HDec.HSyn.sixContactMin_of_open73_cm (r : OpenResearchLeaves54CM) t l`
  (CMBranch/Open73.lean; equivalently `sixContactMin_of_open72_cmbranch2` with the CM inputs in the bundle).
- Readers of the X6 clauses on that route (VERIFIED by reading the copies; clause scan of cm-branch2 clauseuse.txt):
  * through `R1R2fp_r5`: `R1R2fp_Y_r5` (R2fpProps via R2fpProps_of_X6), `residue_unramified_over_branch_r5`
    (R2X6Props + CMExists via cm_of_val), `exists_fibre_object_r5` (X6Surj), `Pin.cm_objects_of_R1R2fp_r5`
    (CMExists + X6Surj.2 + X6Props forget clause), `SGRDirect.elkies_coordinate_r5` (X6 of Elkies' witness);
  * through `R1R2fpRepW_r5`: `R1R2fp_of_rep_r5`, `r1rec_of_rep_r5`, `pairsLift_of_rep_r5` (X6Surj.2),
    `GapST.cm_pointW_r5` (X6Surj, X6Props, R2X6PropsIff), the x6ConicModel producers (X6ConicModel read by 0 constants);
  * the X6 field consumers in the bundles: `gonzalezRotgerX6Ab` (X6 witness -> row), `babaGranathRationalAb` (row's
    R2X6PropsIff), `elkiesX6StarFunctionField -> elkiesX6StarPrinted -> elkiesEquationsX6Ab` (x6ConicModel, and
    sgr-direct's HeckeSqrtBranchAny via SGRFold.heckeSqrtBranchAny_of_open29).
- Every reader except HeckeSqrtBranchAny needs, on Y3: R2fpProps, pi onto P^1(Qbar), the converse CM clauses. All three
  are clauses of y3-p1j's Y3ToP1jAt. HeckeSqrtBranchAny (a global sqrt(c(27X+16)) in the Galois closure) is not.
- New file ZInQKernel/Contrib/OneProof/Y3X6/Row.lean: row `Y3X6.R1R2fpY3` (R1fp, R1hecke, Y3ToP1jAt, R1rec on one Y),
  `r1r2fpY3_of : Y3ToP1j -> RayClassCM -> R1R2fpY3` and the five readers reproved on it.
- Generators scratch/y3-x6/gen/gen_y3.py (copies R5Prune* with _r5 -> _y3, row replaced, X6 producers deleted,
  X6ConicModel_y3 := True, fields gonzalezRotgerX6Ab -> y3row : Y3ToP1j, Elkies fields -> heckeSqrtY3 : HeckeSqrtBranchAny,
  babaGranathRationalAb dropped) and gen_top.py (OpenResearchLeaves55Y3 = 54CM - x6CoarseModuliIdeal - elkiesX6StarEveryIdeal
  + y3ToP1j + heckeSqrtBranchAny; top `HDec.HSyn.sixContactMin_of_open74_y3x6`).
- Merged-tree issue (VERIFIED, lake build): CMBranch/Top2.lean (cm-branch2) fails on this tree: cm-branch d4073125e changed
  `sixContactMin_of_open4_cm` to take `CMHomFieldSplit` (A8.lean: CMFibreSplit reduced to it) while Top2 passes
  `c.cmFibreSplit`. So CMBranch2.lean / R5Prune*.lean / Open73.lean do not build here. Workaround: Y3X6/Base.lean copies
  `CMBranch.CMInputs2` verbatim; the y3-x6 copies use only cm-branch2's `_r5` chain (which has its own copy of open4_cm with
  CMFibreSplit) and never import Top2.
- Compiled (VERIFIED, lake build): Y3X6/Row.lean, Copy1-3.lean (162 blocks; one extra patch: descend_main's obtain),
  Top.lean, Y3X6Fold.lean. Axioms of sixContactMin_of_open74_y3x6, sixContactMin_y3x6, the Row theorems, cm_pointW_y3:
  [propext, Classical.choice, Quot.sound] (scratch/y3-x6/axioms.txt).
- Closure scan (VERIFIED, scratch/y3-x6/Closure.lean -> closure.txt, 129737 constants): X6Props, R2X6Props, CMExists,
  X6Surj, R2X6PropsIff, R5ptProps, X6CoarseModuliIdeal, ElkiesX6StarEveryIdeal, X6CoarseModuli, ElkiesX6StarEvery,
  ElkiesX6StarPrinted, ElkiesX6StarFunctionField, ElkiesEquationsX6Ab, BabaGranathRationalAb, R1R2fpRepW, R1R2fp,
  X6ConicModel: not in the closure. Y3ToP1j, HeckeSqrtBranchAny, R1R2fpY3: in. 0 `_r5` constants.
- grep (VERIFIED, scratch/y3-x6/grep-x6.txt): in Y3X6/* and Y3X6Fold.lean the X6 field names occur in comments only.
- Computed (VERIFIED, scratch/y3-x6/pullback_check.py -> pullback_check.txt): G^6 - 97200 F^2 = H^2 (L515-516);
  27 G^6 (J + 16/27) = 16 H^2, so the pullback orders over 0, oo, -16/27 are 2, 6, 2 (L517); prime support of the
  pairwise resultants/discriminants/leading coefficients of F's six roots, G, H's three quadratics: {2,3,5,7,11,13} (L518).
