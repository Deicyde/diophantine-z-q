# kummer-comp (2026-11-13)

**Verdict: `KummerCompositum` is PROVED in Lean, so `KummerMeetGlue` is a theorem.**
No new hypothesis, leaf or glue Prop. The statement is prop-ts-glue's, verbatim.

**What compiles (VERIFIED):** `lake env lean scratch/kummer-comp/KummerComp.lean` (1 min 05 s)
gives 0 errors, and all 81 `#print axioms` lines are `[propext, Classical.choice, Quot.sound]`.
- The file is scratch/ts-kummer/KummerTS.lean byte for byte (`check_identical.py`: PREFIX
  IDENTICAL), followed by the appendix.
- New theorems (namespace `KummerComp`):
  - `compositum_core`: abstract compositum with a prescribed prime, via a minimal prime of
    `O ⊗_A B` inside the kernel of the residue map, then lying over;
  - `compositum_finrank`: degree bound, via a primitive element;
  - `extend_along`: extending `φ` into `ℚ̄`;
  - `kummerCompositum`, `kummerCompositum_final : PropTSGlue.KummerCompositum`;
  - `kummerMeetGlue : KummerMeetGlue`;
  - `propTSAll_kc`: `PropTSAll` from T2, `R1R2fp`, `MobiusGlue`, `SNSpecialize` and the five
    Hecke Props.

**What remains:** under `PropTSAll`, the open glue is `SNSpecialize` and the five Hecke Props
(hecke-rest). Nothing remains in the Kummer branch. Status lines in ts-kummer.md and
prop-ts-glue.md that call `KummerCompositum` open are out of date (not edited).

Files: docs/research/kummer-comp.md (report), scratch/kummer-comp/ (Core.lean dev file,
KummerComp.lean final, make_final.py, check_identical.py, compile_out.txt, log.md).
