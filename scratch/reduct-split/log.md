# reduct-split results log

Setup: compile checks with `scratch/reduct-split/chk.sh FILE` = `lean` with LEAN_PATH on a symlink tree
`~/rs-lib` of ~/dzq-check2's build (same commit 5da857b0, `git diff 5da857b0 HEAD -- ZInQKernel` empty) plus
`ZInQKernel/OneProof/H/TailY.olean` compiled out of tree (17 s, unchanged source). One Lean process at a time.

## Compile outcomes
- 11:25 Reduction.lean §1 (divisibility: `exists_pow_eq`, `exists_tate_lift` from `PkgI2.TorsionStructure.{0}`): OK, 4 s. VERIFIED.
