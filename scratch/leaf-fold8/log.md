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
- 08:31-08:50 base build (`lake build +ZInQKernel.OneProof.Main`, 19 min: kernel modules and the whole chain
  LPrefix..TailX were out of date). DumpCompact before: 9953 OneProof constants (hashes_before.txt,
  frozenTarget_before.txt).
- 08:52-09:05 `lake build` one module at a time: TailY (14 s), TailZ (13 s), TailZ2 (14 s), TailZ3 (14 s), all at
  the first try; the six Contrib modules (FinitePresentation 35 s, Smooth 22 s, CloudW02 Basic 3 min 38 s,
  CloudW03 Main 1 min 45 s, T11bExists 11 s, EigenformTwist 12 s), exit 0.
- TailZ4 first try: only `r18_lf8`, `r22_lf8` failed (the chain's R18/R22 copies are over leaf-push2's copy of
  `stableFaltingsHeight`, not defeq to the kernel's). Fixed with the chain's proved
  `G0HeightCopies.heightCopiesAgree` and the field-by-field IsCurve/IsJacobian conversion (test/T2.lean). Every
  Contrib proof plugged into its field directly (types and universes `.{0}` matched, incl. W06's `T11bExists` =
  the chain's `AVB2.T11bExists` by unfolding).
- TYZSplit (T11.lean port) 31 s. Main switched to sixContactMin_of_open8 and h33 : TYZSplit.TYZThm33.
  `lake build +ZInQKernel.OneProof.Main`: exit 0; `#print axioms ZInQ.OneProof.frozenTarget`: propext,
  Classical.choice, Quot.sound. DumpCompact after: 10831; cmp_hashes.py: 0 removed, 1 changed (frozenTarget), 878
  new, all in TailY-TailZ4 and TYZSplit.
