# loc-fix (2026-11-12)

**Result.** The repairs of rv-loc-leaves and rv-nocm are applied everywhere they belong. No published
statement of the project still carries any of these four errors:
- T27 without "indefinite";
- `#CM(R) = h(R)`;
- "indices 4, 6, 2" for `X₆ → X₆/W`;
- Lin–Yang "Example 30".

Report: docs/research/loc-fix.md. Log: scratch/loc-fix/log.md.

- **T27 (Lean).** The leaf is now Yu's form `PkgI3.QMDichotomyYu`, with the hypothesis
  `QuatIndefinite a b`, plus `ObjBridge.QMDichotomyYu` and `qmDichotomyYu_iff`. This is done in
  ZInQKernel/HDecomp/Objects.lean and scratch/h-decomposition/Leaves.lean, both `I3Leaves` bundles and
  the HSyn field `t27`. The old, stronger `QMDichotomy` Prop is removed. Its conclusion survives only at
  `B = (2,−3)`, as `PkgI3.qmDichotomy_B6`, proved from Yu's form and `quatIndefinite_two_neg_three`.
- **R02/R05 (rv-nocm §3.1, §3.2 exact texts), R16/R17/R22, and the leftover locators.** Applied in:
  - h-decomposition, glue-repo, hdec-elementary/faithful/alt;
  - h-trust: the A2, A5 and A10 rows, each with a dated review note;
  - pkg-I1, h-b1 (M4), h-v14, wk-h, rv-leaves-a;
  - tyz-t1: `char'` is Lemma 3.14, VERIFIED by counting environments in Period7.tex;
  - HDecomp/Repo/PRArith.lean;
  - Leaves.lean: rv-loc-leaves' patch_leaves.py (16 edits), plus the R03 and QMHauptmodul locators;
  - LadicCond.lean: the Carayol docstrings.

**Compiles (VERIFIED).**
- `lake build ZInQKernel`: exit 0.
- `scripts/print_axioms.lean`: 182 entries. That is 180 plus the 2 added (`qmDichotomyYu_iff`,
  `qmDichotomy_B6`). All are exactly `[propext, Classical.choice, Quot.sound]`.
- `Leaves.lean`: exit 0, with the one known `sorry` (`HSyn.sixContactMin_of_leaves`). Of its 81 axiom
  lists, 80 are standard.
- `LadicCond.lean`: exit 0.

**Remains.**
- Other tasks' scratch copies of the old T27 (obj-bridge, glue-I3-linalg, glue-ssbc, hsyn/tail) are
  outside this task's edit list and unchanged.
- rv-loc-leaves' optional Pazuki fold-in was not copied into Leaves.lean.
- No primary source was re-read (no network). The readings of Yu, González–Rotger, Baba–Granath and
  Carayol are the audit's.
