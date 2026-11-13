# ts-kummer (fleet summary)

**Result: all seven Kummer pieces under `KummerMeetGlue` are proved in Lean, so `KummerMeetGlue`
is a theorem (`TsKummer.kummerMeetGlue`). No statement was changed, and none was found false,
vacuous or inert.**

Proved, in namespace `TsKummer`:

| Piece | Lean name |
|---|---|
| `KummerCompositum` | `kummerCompositum` |
| `KummerAbhyankarFinGlue` | `kummerAbhyankarFinGlue` |
| `KummerOtherBranchFin` | `kummerOtherBranchFin` |
| `KummerVerticalFin` | `kummerVerticalFin` |
| `KummerAbhyankarInfGlue` | `kummerAbhyankarInfGlue` |
| `KummerOtherBranchInf` | `kummerOtherBranchInf` |
| `KummerVerticalInf` | `kummerVerticalInf` |

- The two Abhyankar pieces use exactly the T2 (`PkgI2.AbhyankarDVR`) hypothesis that their
  statements carry.
- General lemmas proved along the way:
  - `unramCompositum`: a compositum of unramified extensions over a DVR is unramified;
  - `unramBaseChange`: unramified base change along any map of DVRs;
  - `ratFunc_transc`: a non-constant `P/Q` is transcendental over ℚ;
  - transfers between ℚ[X], ℚ[1/X] and their localizations.
- Finding: the hypothesis `n < p` in the two vertical pieces is unused.

**Consequence.** `propTSAll_ts'` gives `PropTSAll` from:

- T2, `R1R2fp`, `MobiusGlue`;
- `SNSpecialize` and the five Hecke Props.

That is 6 open glue Props instead of prop-ts-glue's 13.

**What compiles:** `lake env lean scratch/ts-kummer/KummerTS.lean` gives 0 errors in 1 min 5 s, and
every `#print axioms` line is `[propext, Classical.choice, Quot.sound]`. KummerTS.lean is
PropTSGlue.lean verbatim (`check_identical.py`: PREFIX IDENTICAL, apart from 3 extra Mathlib
imports) plus the appendix. The development file is `scratch/ts-kummer/Core.lean`.

**What remains:** nothing among the Kummer pieces. Under Proposition TS the remaining open glue is
`SNSpecialize` and the Hecke pieces (prop-ts-glue's report §6).

Model work; no human review. Details: docs/research/ts-kummer.md, scratch/ts-kummer/log.md.
