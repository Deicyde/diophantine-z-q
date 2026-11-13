# g0-x1belyi results log

Piece: `HSyn.G0Split.X1BelyiOnModel` (missing piece 3 of `scratch/g0-split/Split.lean`).

## 2026-11-13
- Base: merged `origin/wip/g0-split` (c20fa62b) into this branch (it was not in 883c4ddf).
- `defdiff.py`: the declarations `X1BelyiOnModel` depends on (`PkgI3.AbVar`, `AbVar.dim`, `Qj`,
  `Ej`, `Kbar`, `EjBar`, `xCoord`, `fieldX1`, `IsCurve`, `SpecQ`, `IsX1Model`, `RatPt`,
  `IsJacobian`, `IsJ1`, `IsBelyiFunction`, `BelyiX1`) are textually identical in `Split.lean` and in
  `ZInQKernel/HDecomp/{Objects,ModCurves/Defs,ModCurves/Leaves}.lean`; `ffStructMap`/`ffAlgebra`
  differ in form from the kernel's `LeafPush2` copy, so Split's text is copied. VERIFIED (computed).
- `X1BelyiOnModel`, `ffStructMap`, `ffAlgebra` copied into `part_onmodel.lean`; `diff` against
  Split.lean: identical. VERIFIED.
- 01:46 `lake build ZInQKernel.HDecomp.ModCurves.Glue`: OK (9054 jobs).
- 01:48 first draft: 2 errors (comap along `e.symm.toRingEquiv` vs `e.toRingEquiv.symm`).
- 01:49 second: 2 errors (`RatFunc.adjoin_X` does not rewrite: its `Algebra ℚ (RatFunc ℚ)`
  instance is not reducibly the one elaborated for `Qj`; `equivFieldRange` instance mismatch).
  Replaced by a polynomial induction (`mem_adjoin_image`) and `RingEquiv.ofBijective` of a
  `codRestrict`.
- 01:50 `part_onmodel.lean` alone: 0 errors; `x1BelyiOnModel_of_belyiX1 : BelyiX1 → X1BelyiOnModel`,
  axioms [propext, Classical.choice, Quot.sound]. VERIFIED (compiled).
- 01:51 `X1OnModel.lean` (build.sh: x1-belyi body + part_onmodel + part_final, 562 lines), 29 s:
  0 errors, no sorry. `#print axioms` [propext, Classical.choice, Quot.sound] for
  `x1BelyiOnModel_of_belyiX1`, `x1BelyiOnModel_of_leaves`, `x1BelyiOnModel_of_x1Leaves`. VERIFIED.
- FINDING (VERIFIED, read): the bundle leaves `TextbookLeaves.t5 : PkgI2.TorsionStructure` and
  `ResearchLeaves.r7a : PkgI2.NeronOggShafarevich` are stated for abelian varieties as group objects
  in `Over (Spec K)`; x1-belyi's T1/T2 are stated for Mathlib Weierstrass-curve points. Deriving
  T1/T2 from t5/r7a needs the Weierstrass curve as a group scheme (`IsAbelianVariety`) with
  `E(K̄)` identified with its points: not in Mathlib 4.35, not attempted.
