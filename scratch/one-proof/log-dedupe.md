# op-dedupe results log

## Step 1: baseline (2026-11-13 22:55 PST)
- `lake build +ZInQKernel.OneProof.Main`: success, 6m59s wall (11801 jobs; rebuilt part of the tree).
- Main.lean `#print axioms`: `'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]`.

## Step 2a: LF2Stalks, LF3Cot (root namespace) -> HeightBC imports
- Tool: `scratch/one-proof/del_decls.py` (deletes the map's declarations of one module, with attached docstrings and
  `@[..]`/`open .. in` lines; adds the kernel module imports).
- LF2Stalks: 43 of 43 declarations deleted; imports `Contrib.HeightBC.StalkPullback`, `Contrib.HeightBC.LocalStructure`.
- LF3Cot: 6 of 6 declarations deleted; imports `Contrib.HeightBC.StalkTensor`, `Contrib.HeightBC.CotangentBC`.
- `lake build +ZInQKernel.OneProof.Main`: success (5m09s), no edits needed.
