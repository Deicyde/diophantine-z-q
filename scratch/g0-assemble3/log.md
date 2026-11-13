# g0-assemble3 results log

## 2026-11-13
- Merged origin/wip/{local-glue,prop-ts-glue,kf-glue} (all three have reports; no conflicts).
- Base copy: scratch/g0-assemble3/{Leaves.lean, imports_extra.txt, parts/} = scratch/g0-assemble2's (byte copies).
  Leaves.lean is g0-assemble2's copy (root namespace), NOT the current scratch/h-decomposition/Leaves.lean,
  which since moved into `namespace HDec` and imports ZInQKernel/Contrib modules (diff 1411 lines, VERIFIED);
  porting the parts to the HDec version is a separate mechanical step, not done here.
- Prefix build run 1 failed: `unknown module prefix 'ZInQ'` (kernel imports not built in this worktree);
  `lake build` of the five imported modules (replayed, 9066 jobs, OK), then prefix rerun.
- G7Data fix (part 75_modfield.lean): appended the clause `Module.finrank ℚ L ≤ heightD` (G4Out's bound, which
  G7Data dropped; g8-object §4.1 and linked-tate §5 found this). `g7OutUnr_of_g4Out` supplies it from G4Out's
  `hLD`; `g7Out_of_g7OutUnr` drops it.
- TailA with the G7Data clause: run 1, 1 error (part 75 L836 `hdata.2^11` now a pair; fix `.1`, also in linked-tate's copy c10 twice); run 2 VERIFIED exit 0, 0 errors, 65 s.
- TailB (a30 with conj-twist's `[NumberField K]` on ConjUniformization): VERIFIED exit 0, 0 errors, 92 s. TailC: VERIFIED exit 0, 0 errors, 167 s.
- TailE (parts b10 infra-stalks, b20 image-plane, c10-c16 linked-tate): run 1: b20 lacked the `noncomputable section`/`namespace LeafQM.AV.Pin`/opens (ImagePlaneFinal L1715-1724) in which its L2210+ sit (fixed); d20 cut L5266-5276 opened a docstring (fixed: header L5266-5272). Run 3 (TailE = b*, c* only): VERIFIED exit 0, 0 errors, 30 s.
