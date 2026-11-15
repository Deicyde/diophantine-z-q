# ht-exists results log

Base 16db7d60 (wip/ht-bypass, leaf-fold22; frozenTarget over OpenResearchLeaves21). Build tree copied from
~/dzq-wt/ht-bypass (same commit, clean): .lake/build and lean/.lake/build (cp -a --reflink).

## Statements
- Field: `ZInQ.Contrib.HodgeSplit.EigenformHTNew` (TailS.lean l.1275), bundle OpenResearchLeaves21 (research).
- New leaf `EigenformHTExists.KatoHTExists` (existence form, cohomological normalization: geometric Frobenius
  trace a_p, HT weights {0, k-1}, semisimple witness). Same statement as c-to-printed2's KatoRealizationCohSS.
- Restricted leaf `EigenformHTExists.KatoHTExists5Ge3` (l = 5, k >= 3).

## Compile outcomes
- 06:17 `lake build ZInQKernel.Contrib.OneProof.EigenformHTExists`: FAIL, synthInstance timeout
  (Algebra.IsSeparable ℚ_[ℓ] E) in htDual_proof (instance drift under the TailX import, as c-to-printed2 noted).
- 06:19 same with `set_option synthInstance.maxHeartbeats 400000 in` before htDual_proof: OK (17 s), VERIFIED.
  Warnings only: deprecated if_neg/if_pos in the verbatim copy of HTDual.lean.
- 06:19 `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.EigenformHTExists`:
  OK (12987 jobs, all replayed but the new file). VERIFIED.
- 06:20 `lake env lean scratch/ht-exists/Discharges.lean` (output Discharges-output.txt), VERIFIED:
  `DISCHARGES [OpenResearchLeaves21.eigenformHTNew] by EigenformHTExists.eigenformHTNew_of_katoHTExists`,
  still assumes `[KatoHTExists, TateTwistInvariants, AxSenTate]` (the last two are LEAF fields of
  OpenAddedLeaves17), axioms standard; `#discharges: 63 open hypotheses, 1702 theorems checked, 6 discharge one`
  (the other five are the already-folded contributions). `#print axioms` standard for all 7 new theorems.
- 06:20 `autofold.py scratch/ht-exists/autofold.json --dry-run`: `strict count: 46/10 on 56 -> 46/10 on 56;
  strictest 45/11 -> 45/11` (neutral: the leaf is flagged pending reading, counts GLUE). VERIFIED.
- 06:20 dry-run output minus line 1 = FoldDryRun.lean; `lake env lean`: OK, `sixContactMin_of_open29` standard
  axioms (FoldDryRun-output.txt). VERIFIED.
- 06:21 added §9 `afterG7_of3Kato5` (AfterG7 from KatoHTExists5Ge3 via ht-bypass's afterG7_of3Weak): first build
  FAIL (AfterG7 auto-bound: missing `open _root_.HDec.G0ModField`); with the opens and file-wide
  `set_option autoImplicit false`: OK (18 s). No auto-bound identifier anywhere in the file. VERIFIED.
- 06:22 rebuild of Main/Discharges/contribution OK; Discharges re-run: same DISCHARGES line, 1703 theorems checked,
  6 discharge one; 8 `#print axioms` standard (incl. afterG7_of3Kato5). FoldDryRun re-compiled OK. VERIFIED.
- Scan: no #eval/run_cmd/initialize/syntax/notation/macro/elab/axiom/sorry in the contribution. VERIFIED.
