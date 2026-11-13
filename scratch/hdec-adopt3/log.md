# hdec-adopt3 results log

## Duplicate scan (scratch/hdec-adopt3/dups.py: same last name component, whitespace-normalized block)
- ModCurveLeaves §B: `Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform
  scaleH oldSpace IsNewform` are identical to `PkgI4.*` of `Conductor/LadicCond.lean`.
- ModCurveLeaves §A: `firstColMod firstCol_algebra firstColMod_eq_iff index_Gamma1_le` are
  identical to `GlueAssembly.*` of `Assembly/E2Index.lean`.
- Faltings §15: `AbVar` (structure + instance attributes), `AbVar.baseChange`, `AbVar.dim` are
  declared copies of `PkgI3.AbVar` (Objects); bodies equal, only docstrings / `noncomputable` /
  universe (`Type` vs `Type u`) differ.
- QMLeaves: no copy of HDecomp code except the one-line `abbrev Qbar` (kept). `LeafQM.O`,
  `LeafQM.B` differ in construction from `GlueRepo.A1.O` (kept).
- T32a.lean lines 17-1816 = glue-b3b's B3b.lean lines 11-1810 (diff, VERIFIED); new part from
  the comment "# glue-t32a".

## Build 1 (19:5x PST): `lake build` of the four leaf modules (T32a, ModCurves.Glue, QM.Leaves,
Faltings.Leaves) and their dependencies: exit 0. All 13 new modules built; warnings only
deprecations / unused-tactic / module-system import notes (no `sorry` warning).

## Statement check (same.py, VERIFIED)
Kept declarations identical (whitespace-normalized statement and proof) to the drafts: T32a 19/19
(after the copied B3b part), ModCurveLeaves 84/99, QMLeaves 143/143, Faltings 133/138. Missing:
the 15 ModCurves copies (PkgI4 x11, GlueAssembly x4), Faltings `AbVar`, `AbVar.baseChange`,
`AbVar.dim` (copies of PkgI3's) and `AbVar.structMapOn`, `AbVar.origin` (renamed to
`PkgI3.AbVar.structMapOn`, `PkgI3.AbVar.origin` so dot notation in `IsEllipticCurveOf` resolves).
grep: no `sorry`/`admit`/`axiom` in the 13 modules; awk: no line > 100 characters.

## Build 2 (19:46 PST): `lake build ZInQKernel` exit 0 (9980 jobs), after the last Lean change.
## Axioms (19:46 PST): `lake env lean scripts/print_axioms.lean` exit 0: 332 entries (272 + 60
new), all exactly [propext, Classical.choice, Quot.sound]; list in scratch/hdec-adopt3/axioms.txt.
