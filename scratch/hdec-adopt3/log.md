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
