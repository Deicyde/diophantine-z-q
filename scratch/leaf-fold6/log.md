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

## 02:40-02:50 Check6 and verbatim checks (dev chain), VERIFIED
- olean/Check6.lean (45 s): `example : ∀ r t l g, _root_.ZInQ.SixContactMin := HDec.HSyn.sixContactMin_of_open6`
  compiles; axioms of open6 and open6_poincare standard; closure 184 758 constants (open6_poincare 184 795), no
  sorryAx; contains gammaStarGen_proof, valenceBound_of_formula, ellipticOrderLe6_proof, cmDescends_of,
  torsionDescends_of_t5, base2_of_base3, qmHauptmodul_of_base2, orbit4/3/24, LQ20.s20WeightExact_of, t8_ofK6,
  t11b_of_exists, torsionStructure_ofK5, heckeVertWitness_of_leaves5; open6 does NOT contain
  poincareReducibility_of_simpleImage (open6_poincare does).
- Field heads: 68 fields, 32 on kernel constants (leaf-fold5's 33 minus poincareComplement, simpleImageIsogeny, plus
  t8 = kernel `PkgI3.PoincareReducibility`). Expr check: every field type of OpenTextbookLeaves6 / OpenAddedLeaves6 /
  OpenGlue6 is `==` the same field's type in OpenTextbookLeaves5 / OpenAddedLeaves5 / OpenGlue5 / OpenAddedLeavesQ10,
  and t8 is the constant `PkgI3.PoincareReducibility`: ALL MATCH. (First run: t23 failed only because the check
  telescoped through the field's own ∀; fixed to strip only the structure binder.)
- py/verbatim_check6.py → py/verbatim_check6_out.txt: ALL OK. (A) 41 field lines identical to their source bundles'
  text; (B) every chain head constant has an identical declaration in a non-assembly source file (r1r2, r5, r5count:
  identical statement, docstring repaired since); the 32 kernel heads found in ZInQKernel/; (C) kernel
  PkgI3.PoincareReducibility = pkg-I3's I3.lean (with docstring) = the chain's copy (statement); (D) STQM,
  TorsionDescends, ValenceFormulaGammaStar, ellOrder, EllipticOrderLe6, QMHauptmodulBase(2,3), x3 identical in f10,
  Fold.lean and leafq-check's standalone files.
