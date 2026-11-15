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
