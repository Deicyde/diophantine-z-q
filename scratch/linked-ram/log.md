# linked-ram results log

## 2026-11-13 setup
- Merged origin/wip/linked-tate (already in base), origin/wip/lt-goodred, origin/wip/g0-assemble3 (clean).
- Oleans: copied g0-assemble3's built olean chain (LPrefix, TailA-C, E, F; `~/dzq-wt/g0-assemble3/scratch/g0-assemble3/olean/`)
  into scratch/linked-ram/olean/ (gitignored). ZInQKernel imports of the prefix are unchanged between that worktree and this
  one (diff only in Contrib/TYZGenus, GZTheta, ModularForms; not imported). VERIFIED (git diff --stat).
- g0-assemble3 already redid linked-tate's reduction on the corrected G7Data: `GluePieces4` fields 45 `kernelFieldBreaks`,
  46 `tateRamAtThree`, via `UnramTate.linkedRam_of` (part c12, verbatim linked-tate 98b). VERIFIED (read).

## Findings
- F1. `UnramTate.TateRamAtThree` (part c12) is NOT quantified over G7Data: it ranges over all `K ≤ L ≤ L'` and every
  `QML3 K`, with no bound on `[L:ℚ]`. So g0-assemble3's G7Data fix does not reach it; linked-tate's own caveat ("justified
  only for small K") still applies to GluePieces4 field 46. VERIFIED (read c12 L107-118). Truth for unbounded K: SPECULATIVE
  (likely false: inertia image at 3 can be cut out by a field whose upper break exceeds U0 when K's breaks are near U0).
