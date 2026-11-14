# op-compact log

## Step 1: baseline (commit 053cbad0)
- `lake build +ZInQKernel.OneProof.Main`: OK (full rebuild of the OneProof modules, ~12 min wall).
- `lake env lean scratch/one-proof/DumpCompact.lean` > dump_before.out: frozenTarget type -> frozenTarget_type_before.txt;
  axioms `[propext, Classical.choice, Quot.sound]`; hashes of type and value of all 8202 constants of the
  `ZInQKernel.OneProof` modules -> hashes_before.txt.
- Sizes before: 80137 lines, 8224119 bytes in ZInQKernel/OneProof/H (1089 tagged alias opens removable).
