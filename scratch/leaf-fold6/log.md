# leaf-fold6 results log

## 2026-11-14 02:30 start
- Base d5d43efc (wip/w54). No earlier run (no log.md).
- Inputs: leaf-fold5 (scratch/leaf-fold5/, olean chain LPrefix ... TailK (leaf-fold4's sources) + TailL, TailM, TailN;
  `HDec.HSyn.sixContactMin_of_open5`, 26 + 21 + 21 + 2 = 70) and leafq-check (scratch/leafq-check/Fold.lean,
  `import TailK`; `sixContactMin_of_open10`, 26 + 19 + 19 + 1 = 65 over leaf-fold4's bundles).
- The kernel modules the chain imports (scratch/leaf-fold5/kernel_targets.txt) are unchanged between leaf-fold5's base
  ee7582da and d5d43efc (`git diff --stat ee7582da d5d43efc -- ZInQKernel` touches only Contrib/TYZChain and
  AllContrib), so leaf-fold5's chain sources compile against this worktree's kernel build.
- Plan: module TailO (`import TailN`) = leafq-check's Fold.lean body (its OpenAddedLeaves5..10 and
  sixContactMin_of_open5..10 renamed to OpenAddedLeavesQ5..Q10, sixContactMin_of_openQ5..Q10; leaf-fold5's names kept)
  + part f20 (new bundles, `sixContactMin_of_open6`).
- T8 (goal (b)): keep T8 as a textbook field over the kernel's `_root_.PkgI3.PoincareReducibility` (Objects.lean),
  transported by `t8_ofK6`; glue 1. The other way (PoincareComplement + SimpleImageIsogeny) is compiled as a corollary.

## 02:34 TailO compiles (dev check against leaf-fold5's compiled chain in its worktree), VERIFIED
- mk_f10.py: part f10 = Fold.lean minus `import TailK`, 52 renames (OpenAddedLeaves5..10 → Q5..Q10,
  sixContactMin_of_open5..10 → openQ5..Q10, openAddedLeaves4_of_5, openAddedLeaves5_of_6), asserted reversible.
- part f20: `t8_ofK6`, `OpenTextbookLeaves6` (21), `OpenAddedLeaves6` (20), `OpenGlue6` (1), `cmDescends_of6`,
  `qmHauptmodul_of6`, `textbookLeaves4_of_open6`, `addedLeaves4_of_open6`, `glue4_of_open6`,
  `sixContactMin_of_open6` (26 + 21 + 20 + 1 = 68), `sixContactMin_of_open6_poincare` (69, glue 2),
  `addedLeaves5_of_open6`.
- olean/TailO.lean (import TailN): exit 0 in 40 s, 0 errors, no sorry; all 21 axiom lines standard
  (dev.sh: LEAN_PATH = leaf-fold5 worktree's chain oleans + its lake packages; not committed).
