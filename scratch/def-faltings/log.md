# def-faltings results log

## 2026-11-12

- Faltings.lean created: sections 1-14 copied from scratch/bp-faltings/Hodge.lean (namespace
  ZInQ.DefFaltings); new sections 15-18: AbVar/GroupModel (copied), Hodge line of a group model
  (cotangent, omegaAt, omega, hodgeSpace, detLattice, wedge), complex points Pts, evalAt, dom,
  IsAnalyticUniformization, germAlong, jacDet; gap Props AnalyticUniformizationExists,
  AnalyticUniformizationUnique, HodgeLatticeTheorem; MetrizedModel, FinExt,
  stableFaltingsHeight (EReal infimum), stableFaltingsHeightDeligne; theorems
  stableFaltingsHeight_le, le_stableFaltingsHeight, stableFaltingsHeightDeligne_eq.
  Compile: `lake env lean scratch/def-faltings/Faltings.lean`: no errors (VERIFIED).
- Added §19 AT1: AbVar.structMapOn, AbVar.origin, IsEllipticCurveOf, AcceptanceEC (Prop,
  unproved), stableFaltingsHeight_eq_faltingsHeightEC (conditional form, proved);
  §20 AT2: Genus2Eq/faltingsHeightGood (copied from pkg-I5), HodgeData.modelHeight_eq_faltingsHeightGood
  and stableFaltingsHeight_eq_faltingsHeightGood (conditional forms, proved);
  §21 leaves: IsIsogeny, isogDeg, grKappa, R19_GaudronRemond, R20_FaltingsLemma5, R21_Bost (Props),
  stableFaltingsHeight_ne_bot_of_R21 (proved). Compile: no errors, no warnings (VERIFIED).
