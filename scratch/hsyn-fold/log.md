# hsyn-fold results log

## Leaves.lean edits (scripts fold.py, fold2.py in this directory; then two hand fixes)
- Added `GlueA6Alg.Alg` (glue-a6-alg A6.lean 47-521); `PkgI2.quatUnipotentTrivial` proved;
  old A6 renamed `PkgI2.goodReduction_of_QM_rational3_of_alg`; `PkgI2.goodReduction_of_QM_rational3`
  now takes only hNOS hRay hTors; `PkgI2.goodReduction_of_QM_rational3'` drops `w, hw`.
- Added `PkgI3.trace_indep_of_ell`, `trace_eq_trace_of_ell` (glue-c10 Trace.lean, without its pkg-I3 copy).
- Added `GlueC10` (C10.lean whole), `GlueD1Local` (Local.lean without its Breaks.lean copy).
- Added `LeafPush` (Push.lean with its pkg-I2 copy replaced by `open PkgI2`), `PkgI4.T23_FontaineClosure`
  (PushDR.lean section Fontaine). Removed the opaque R08, T09, T23, T29, T32; bundle fields now point
  to the concrete statements. 19 → 14 opaque.
- obj-bridge NOT adopted (see note §2.3/§5): its §C-§F were not tried in this file for lack of time.

## Compile
- `lake build ZInQKernel.Hypotheses.JHeight`: success (17 s, 00:10 PST).
- `lake env lean scratch/h-decomposition/Leaves.lean` run 1 (00:14): 1 error (off-by-one copy of Trace.lean line 349), fixed.
- run 2 (00:16, 1m32s): no errors; one `sorry` warning (HSyn.glueOutputs_of_leaves, line 11636).
  69 `#print axioms`: all `[propext, Classical.choice, Quot.sound]` except `HSyn.sixContactMin_of_leaves` (adds sorryAx).
  0 `axiom`, 14 `opaque`.
