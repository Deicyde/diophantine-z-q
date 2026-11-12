# pn-final log

Task: prove `finalStep` in scratch/pn-design/PropN.lean (prefix `final_`).

## Step 1
- Scratch copy scratch/pn-final/Final.lean (PropN.lean with the proof filled in).
- `lake env lean` first failed: `unknown module prefix 'ZInQ'` (the `lean/` package had no build in
  this worktree). `lake build ZInQKernel`: built the `ZInQ` package and the project (no Mathlib rebuild),
  success, 5 min 29 s.
- Attempt 1: errors (`rw [← hy]` direction in hW; `(2 * y).re` from simp order in hzre).
- Attempt 2: `Zsqrtd.re_ofNat` leaves `↑2`; added `Nat.cast_ofNat`.
- Attempt 3: "No goals" after `rw [e1, e2]` in hzre; removed the trailing `push_cast; ring`.
- Attempt 4: Final.lean compiles; only sorry warnings are lemmaN1_core, lemmaN2, matching.

## Step 2: move into PropN.lean
- Copied Final.lean to scratch/pn-design/PropN.lean. `git diff`: 103 insertions, 1 deletion (the
  `sorry` of finalStep). New names: `final_reHom`, `final_imHom`, `final_reHom_apply`,
  `final_imHom_apply`, `final_two_dvd_of_dvd`, `final_four_nsmul_τ` (lines 175–203, directly above
  finalStep's docstring).
- `lake env lean scratch/pn-design/PropN.lean`:
  - 154:8 `declaration uses sorry` (lemmaN1_core)
  - 168:8 `declaration uses sorry` (lemmaN2)
  - 207:59 unused variable `hn` (in the fixed statement of finalStep; not used by the proof)
  - 290:8 `declaration uses sorry` (matching)
- `#print axioms ZInQ.PropN.finalStep` (in the scratch copy): [propext, Classical.choice, Quot.sound].
