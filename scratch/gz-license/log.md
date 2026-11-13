# gz-license results log

1. `git merge origin/main` (main 578fb953): one add/add conflict,
   ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Basic.lean; the two sides differ only by
   main's line `-- Modified for the Z-in-Q kernel: explicit IsSMulApply … arguments` (VERIFIED,
   diff of stages :2 and :3). Took main's version. No other conflict. Merge commit 09735e9b.
2. diffcheck2.py before (scratch/gz-license/diffcheck-before.txt), VERIFIED:
   IDENT 1395, NOTE-ONLY 0, MOD-NOTED 9, MOD-UNNOTED 20, NOPROV 39.
   MOD-UNNOTED = 19 kw-new files (commit-97a5b235 provenance) + gz-decomp's
   NumberTheory/ModularForms/LFunction/Sign.lean. Kinds of change (read in diffs, VERIFIED):
   - 16 files: extra imports of Backport/ modules only (ClassFormation and Kummer/Index also
     replace one import by its Backport/ version);
   - GroupTheory/GroupAction/Norm.lean: groupNorm/groupNormHom block omitted (provided by
     imported oct16 GroupCohomology.Cocycle) + 2 imports;
   - NumberField/InfinitePlace/Completion/Real.lean: exists_completionNormalizedAbsValue_eq omitted
     (provided by oct16 Completion.Basic);
   - Topology/Algebra/Star/Completion.lean: explicit continuity proofs instead of fun_prop;
   - ModularForms/LFunction/Sign.lean: ModularForm.L unfolded (no L_apply_of_ne_zero).
   Notes inserted by scratch/gz-license/addnotes.py, commit after step 2.
   diffcheck2.py after (diffcheck-after.txt): IDENT 1395, NOTE-ONLY 0, MOD-NOTED 29,
   MOD-UNNOTED 0, NOPROV 39 (VERIFIED).
3. Files added on this branch relative to main: 45 vendored modules, all commit 5a01f5fe3621
   provenance (scratch/gz-license/new-modules.txt); all are in scratch/gz-decomp/tc-modules.txt
   (257 lines). NOTICE updated (gz-decomp source entry, 20 files added to modified list).
   Finding: NOPROV = 37 Backport/ files + MathlibBackport/Sylow.lean + Notice.lean. 36 Backport/
   files carry the "Backported from Tau Ceti" line; Backport/Mathlib/Polynomial.lean does not:
   it has a Tau Ceti copyright header but its comment says the proof was written for the backport
   (VERIFIED, read). Recorded in NOTICE; file not edited (rules).
4. `lake build` of the 20 noted modules (one lake run, 1m23s): "Build completed successfully
   (5893 jobs)", all 20 listed as Built, no `sorry` (VERIFIED, scratch/gz-license/build.out).
