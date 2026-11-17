# javanpeykar-rebase (2026-11-16)

**Result.** `javanpeykarBound` is proved over height-fix's sound printed stable height. The proof is
`JavanpeykarRebase.javanpeykarBound_of_printed_rebase_final : JavanpeykarPrintedMap →
ConstantFieldExtensionUnramifiedFinite → MumfordTorsionAlgClosed → ZInQ.HeightFix.SemiAbelianDescendsPerfect →
JavanpeykarBound`, in `ZInQKernel/Contrib/OneProof/JavanpeykarRebase.lean`. It uses only the standard axioms.

- `JavanpeykarPrintedMap` is javanpeykar-fix's leaf verbatim, over `ZInQ.HeightFix.IsPrintedStableHeight`.
  `javanpeykarPrintedMap_of_fix` shows it is never stronger than javanpeykar-fix's leaf.
- Stichtenoth is narrowed to finite `K'/K`. The only consumer uses `K' = K̄`, so the algebraic case is proved
  from the finite one in Lean (`full_of_finite`). `finite_of_full` proves the converse, so the two forms are
  equivalent.
- Every step between the print and the kernel is proved except height-fix's glue `SemiAbelianDescendsPerfect`
  (semistability over `κ̄(𝔭)` ⇒ over `k(𝔭)`, used for kernel height ⇒ printed height). height-fix's other two
  discharges use the same glue.

**What compiles (VERIFIED).**
- `lake build +Main +Discharges +JavanpeykarRebase` succeeds.
- `#discharges` reports that `javanpeykarBound` is discharged with standard axioms
  (`scratch/javanpeykar-rebase/Discharges-output.txt`).
- Autofold:
  - `autofold.json` (this fold alone) and `autofold-with-height-fix.json` (combined with height-fix's two
    discharges) both pass the dry run.
  - Both generated modules compile, and `sixContactMin_of_open39` uses only the standard axioms.

**Count (target −1 GLUE): not met by this fold alone.**
- PrintedMap is entered as kind consequence (review fix 1).
- Alone: 16/21 → 17/22 (+1 GLUE, because the descent glue is a new row; needs `--allow-rise`).
- Combined with height-fix: javanpeykarBound's marginal effect is GLUE 0, LEAF +1.
- After a reading rates PrintedMap LEAF: −1, measured by dry run.
- Proving `SemiAbelianDescendsPerfect` would give another −1. A `semiab-descend` worktree exists.

**Leaf ratings.**
- `JavanpeykarPrintedMap`: printed form, pending reading, kind consequence.
- `ConstantFieldExtensionUnramifiedFinite`: printed form, unread; Stichtenoth 3.6.3(a) is UNVERIFIED.

**Remains.**
- A statement check of Javanpeykar Thm 1.1.1.
- `SemiAbelianDescendsPerfect`.
- height-fix's own spec reads the removed field `{t}.uniformizationLeafAll`. The combined spec fixes that.

Report: `docs/research/javanpeykar-rebase.md`.
