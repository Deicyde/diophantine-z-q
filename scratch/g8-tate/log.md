# g8-tate results log

## Step 0 (2026-11-13 09:03-09:18 PST): environment
- Merged origin/wip/local-glue (origin/wip/g8-object already in the base).
- `lake build` of the kernel modules imported by g8-object's and local-glue's files (incl.
  `ZInQKernel.Main`, `ZInQKernel.Contrib.AbVarBC.Dim`): 6 min, success.
- `build_prefix.sh` assembles `Prefix.lean` (10 791 lines, not committed: generated) =
  `scratch/g8-object/G8Object.lean` (verbatim) + `scratch/local-data/part_local.lean` (verbatim, in a
  `noncomputable section`) + local-glue's parts (verbatim, without `galois_block.lean`, whose text is
  already in G8Object.lean).
- Compile (VERIFIED): `lake env lean -o olean/Prefix.olean Prefix.lean`: 2m10s, 0 errors, no sorry;
  133 `#print axioms` reports, all `[propext, Classical.choice, Quot.sound]`.
