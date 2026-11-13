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
- Added §18 UnifIndep: GroupModel.semilinear_ext_wedge, GroupModel.jacDet_comp (chain rule),
  MetrizedModel.modelHeight_eq_of_model_eq (given AnalyticUniformizationUnique),
  GroupModel.height, GroupModel.height_eq, stableFaltingsHeight_eq_iInf_height (all proved).
- Added NeronSec: GroupModel.IsNeronModel (Néron mapping property), StableHeightFinite,
  NeronModelMinimal (H5 statements), faltingsHeight (toReal) and faltingsHeight_coe (proved).
- Added §22 (R18, R22: missing objects) and #print axioms block.
- Compile (17:00): `lake env lean scratch/def-faltings/Faltings.lean`: no errors, no warnings;
  every #print axioms line lists [propext, Classical.choice, Quot.sound] (VERIFIED).
- Added GroupModel.omegaAt_genericPt (sanity: local lattice at the generic point is all of ω_{A_L}); proved, compiled (VERIFIED).
