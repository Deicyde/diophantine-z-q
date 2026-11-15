# triage2 results log (base 9a100aa7)

## Setup
- lean/.lake missing in worktree -> probes run with scratch/triage2/run.sh (LEAN_PATH + ~/dzq/lean/.lake, same lean/ZInQ tree 02e27597).
- Trace.lean: worklist trace of field projections through bundle converters in the closure of ZInQ.OneProof.frozenTarget.

## Agent reports (SPECULATIVE until re-checked)
- agent-H (R5 heights): no removal; all four feed heightRowsNo20_of8 (TailZ4:153) -> R18/R19/R21/R22; GR reverse-isogeny use needs existence only (bypass via milneIsogenyQuasiInverse, weakening only).
- agent-G (R7): no removal; all uses on the u-family QM surface A (p=5 for HT/dR; l=3,5 for dsThm965, r9a, r9b surjective half).
- agent-R (R1 semistable): r6 uses only QM surfaces over number fields; SS1/SS2/SS3 used for all height-row A incl. J1(N)_L.
  Candidate removal: semistablePersistsSHcp via (b) Raynaud-at-every-L'⊇K'3K'4 + SemistableLocalGlobal (bypass fold) or
  (a') derive SemistablePersistsDVRnf from sga7_IX_3_3 (3.3 second assertion ⇒ first). To verify.
## Run 2 (05:32)
- Trace.lean launched (background); agents X (BG, DelX6), W (GR x2), T (hCM, h33), Y (DelY3 narrow + GLUE notes) launched.
