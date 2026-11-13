# prop-ts-glue results log

Task: reduce `PropTSRed.SpecNonMeeting`, `PropTSRed.KummerMeetGlue`, `PropTSRed.CoverModelOfHecke`
(scratch/prop-ts/PropTS.lean, merged from origin/wip/prop-ts) to smaller named Props or prove them.

## Step 1 (08:01): file and first reduction, compiled
- `scratch/prop-ts-glue/PropTSGlue.lean` = `scratch/prop-ts/PropTS.lean` verbatim (prefix check:
  `check_identical.py` prints PREFIX IDENTICAL, VERIFIED) + `Appendix.lean.part` (namespace `PropTSGlue`).
- Build: `lake build ZInQKernel.HDecomp.QM.Pin ZInQKernel.HDecomp.Descent.B2Glue` OK; then
  `lake env lean scratch/prop-ts-glue/PropTSGlue.lean`: 0 errors, 6 linter warnings (prefix and
  appendix style), all `#print axioms` = [propext, Classical.choice, Quot.sound] (VERIFIED,
  compile_out.txt).
- Part A: `specNonMeeting_of_pieces : PurityGlobalDim2 → SNLocalData → SNHeightOne → SNSpecialize →
  SpecNonMeeting` (PurityGlobalDim2 copied verbatim from t-purity3, proved there). Proved helpers:
  `exists_secIdeal` (the maximal ideal (p, dX − a) as a kernel to 𝔽_p), `not_dvd_den_of_nonneg`,
  `regular_dim2_intPoly` (copied from prop-ts/ZXRegular.lean), `locAlg` (ℤ[X]_m → E).
- Part B: `kummerMeet_of_cases : KummerMeetFin → KummerMeetInf → KummerMeet`;
  `kummerMeetFin_of_pieces : KummerCompositum → KummerAbhyankarFin → KummerOtherBranchFin →
  KummerVerticalFin → KummerMeetFin` (the p-adic bookkeeping t − b = p^M u, c = u^{n−1},
  s₀ = p^{M/n} u is proved); `kummerMeetGlue_of_pieces`.
- Part C: `coverModelOfHecke_of_pieces : HeckeNormalization → HeckeDegree → HeckeBranch →
  HeckeNoVertRam → CoverModelOfHecke` (via prop-ts's `coverModel_of_N`).
- Part D: `propTSAll_of_pieces` (the composite).

## Step 2 (08:15): the case at ∞, compiled
- Added `KummerAbhyankarInf`(+`Glue`), `KummerOtherBranchInf`, `KummerVerticalInf` and
  `kummerMeetInf_of_pieces` (t = p^{−M} u, c = u^{1−n}, s₀ = p^{M/n}/u, c/s₀^n = t; the meeting
  polynomial `b' s^n − c` has f(s₀) = c(b' − t)/t, a p-unit), `kummerMeetGlue_of_pieces'`
  (eight pieces, T2 only through the two Abhyankar steps). `propTSAll_of_pieces` now uses it.
- Compile: 0 errors; 14 PropTSGlue `#print axioms` lines, all standard (VERIFIED).
