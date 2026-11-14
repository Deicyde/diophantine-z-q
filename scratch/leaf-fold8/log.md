# leaf-fold8 results log

## 2026-11-14 08:30 PST start
- Base e9240be8 (wip/w58). OneProof top: HDec.HSyn.sixContactMin_of_open7 (69 fields: 29 + 23 + 16 + 1), strict
  LEAF/GLUE 38/31 (leaf-fold7.md).
- Read reports: leaf-fold7, height-split, height-glue, qm-glue, qm-split, tyz-split; located the six cloud-worker
  Contrib proofs (CloudW01Spread x2, CloudW02Connectedness, CloudW03NeronSurj, CloudW06PoincareRigidity,
  CloudW08EigenformTwists).
- 08:31 started base `lake build +ZInQKernel.OneProof.Main` (kernel modules out of date in this worktree).
- 08:40-09:10 plan (decision rule of leaf-fold7 §5): take height-split+height-glue (strict GLUE -2 under the
  forms used: SS1-SS3 consequence, the other five published), qm-glue H-87/H-88 (-2), the six Contrib proofs
  (-6 fields), tyz-split T-11 (frozenTarget's h33). Not taken: H-3 r5count (CMDescent bundles Albert's
  classification, QMUniformizationC is by its own docstring "not one printed statement": consequence ->
  published + consequence + composite raises the strict count), H-1/H-43 (CoarseFactor + ReciprocityOfFine
  glue: neutral or worse).
- Generated TailY, TailZ (Rows.lean halves), TailZ2, TailZ3 (HauptGlue.lean minus leafq-check's Fold part, which
  is in TailO), OneProof/TYZSplit.lean (T11.lean) with mk_modules.py; verbatim_check8.py: ALL OK. Drafted TailZ4
  (bundles Open*8).
