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

## Merges (00:17 PST): all five extra reports had landed and merged without conflict:
def-ladic-cond, glue-rho-cont, glue-b3-unram, glue-sqrt-local, glue-vigneras. Not folded into
Leaves.lean (cited in the note only).

## obj-bridge (fold3.py)
- Appended Objects.lean §C-§F (lines 1129-1795) without its §A/§B copies.
- run 3 (00:21): §F `homRankBound_of_homFreeFinite` fails: `failed to synthesize AddCommMonoid (Hom A B)`
  at `LinearIndependent ℤ f`, then whnf heartbeat timeout; run 4 with maxHeartbeats 1e6 and
  synthInstance.maxHeartbeats 4e5: same instance failure. §F removed (comment left in the file).
- run 5 (00:25, 1m31s): exit 0, no errors; 1 `sorry` warning (HSyn.glueOutputs_of_leaves);
  81 `#print axioms`, all [propext, Classical.choice, Quot.sound] except HSyn.sixContactMin_of_leaves
  (sorryAx). 14 opaque, 0 axiom, 12404 lines.
- run 6 (00:29, final file, after header/note edits): exit 0, 0 errors, 1 `sorry` warning, 81
  `#print axioms`, all [propext, Classical.choice, Quot.sound] except HSyn.sixContactMin_of_leaves.
