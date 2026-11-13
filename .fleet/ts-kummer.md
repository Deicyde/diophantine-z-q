# ts-kummer (fleet summary)

**Result: six of the seven Kummer pieces under `KummerMeetGlue` are proved in Lean. The seventh,
`KummerCompositum`, remains open glue (true; plan in docs/research/ts-kummer.md §4). No statement
was changed or found false.**

Proved, in namespace `TsKummer`, all with `#print axioms` = `[propext, Classical.choice,
Quot.sound]`:

| Piece | Lean name |
|---|---|
| `KummerAbhyankarFinGlue` | `kummerAbhyankarFinGlue` |
| `KummerAbhyankarInfGlue` | `kummerAbhyankarInfGlue` |
| `KummerOtherBranchFin` | `kummerOtherBranchFin` |
| `KummerOtherBranchInf` | `kummerOtherBranchInf` |
| `KummerVerticalFin` | `kummerVerticalFin` |
| `KummerVerticalInf` | `kummerVerticalInf` |

The two Abhyankar pieces use exactly their own hypothesis, T2 (`PkgI2.AbhyankarDVR`). Two general
DVR lemmas are proved along the way: `unramCompositum` (a compositum of unramified extensions is
unramified) and `unramBaseChange` (unramified base change).

Consequences, also compiled:

- `kummerMeetGlue_of_compositum : KummerCompositum → KummerMeetGlue`.
- `propTSAll_ts`: `PropTSAll` from
  - T2, `R1R2fp`, `MobiusGlue`;
  - `SNSpecialize`, `KummerCompositum`, and the five Hecke Props.

  That is 7 open glue Props instead of prop-ts-glue's 13.

**What compiles:** `lake env lean scratch/ts-kummer/KummerTS.lean` gives 0 errors in 1 min 42 s.
KummerTS.lean is PropTSGlue.lean verbatim (`check_identical.py`: PREFIX IDENTICAL, apart from 3
extra Mathlib imports) plus the appendix.

**What remains:** `KummerCompositum`, which needs a factor `E'` of `E ⊗ ℚ(s)` with a prime over
`s − s₀` above the given prime `𝔓`. The construction is via a minimal prime of `O ⊗ B`;
docs §4 gives the steps.

Model work; no human review. Details: docs/research/ts-kummer.md, scratch/ts-kummer/log.md.
