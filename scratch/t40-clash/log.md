# t40-clash results log

- 17:47 Reproduced: scratch/t40-clash/Clash2.lean (imports GroupWithZero.Units.Basic then
  Backport.Algebra.Group.Units.Basic) fails: "environment already contains
  'Units.val_mul_zpow_natCast_mul' from ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic".
  Three names clash, not one: TauCeti.mem_range_iff_exists_units_map_eq,
  Units.val_mul_zpow_natCast_mul, Units.val_mul_zpow_neg_natCast_succ_mul (Backport copies are the
  commit-4d91513e generalizations: local monoid hom / DivisionCommMonoid).
- 17:48 Fix: Backport/Algebra/Group/Units/Basic.lean drops the three clashing declarations and
  public-imports ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic; header note and
  NOTICE modified list updated. Clash2.lean now compiles.
- 17:48 Static scan (scratch/t40-clash/dupscan.py, heuristic): no other declaration name is declared
  both in T40's import closure (350 files, rdeps/closure) and in a tracked module outside it
  (only false positives from docstring words such as "theorem of").
- 17:51 `lake build ZInQKernel.Contrib.RLeaf.T40 ZInQKernel.Contrib.RLeaf.TateCuspTorsion`: success
  (3m, 0 errors). These two targets cover every module that imports the changed file
  (scratch/t40-clash/rdeps.py: Backport TateCurve CoordinateEvaluation, Equation, Line, XCoordinate,
  Uniformization, Injectivity, Homomorphism; RLeaf TateCusp, TateCuspMuN, TateCuspTorsion, T40).
- 18:00 `lake build` of Mobius.Main, FrobPieces.SmoothGeomConnIntegral, Chebotarev.FrobeniusDense,
  AbsFrob.Basic, GZTheta.ALFinal, RLeaf.T36Torsion: success (10690 jobs, 8.5 min, 0 errors).
  `lake env lean scratch/t40-clash/Together.lean` (T40 + those six + the vendored
  GroupWithZero.Units.Basic): compiles, all #checks print (7 s).
  Note: none of the six required modules imports GroupWithZero.Units.Basic (forward closures), so
  the explicit import of that module in Together.lean is what exercises the former clash.
  Next: broader test, T40 + all 74 top-level Contrib modules (1105 modules still unbuilt).
- 18:16 `lake build` of all 74 top-level Contrib modules (scratch/t40-clash/contrib-tops.txt;
  together their closures are all of ZInQKernel/Contrib/): success (11928 jobs, 15.7 min, 0 errors).
- 18:16 scratch/t40-clash/AllContrib.lean (T40 + all 73 other tops): fails, but on a clash NOT
  involving T40: 'Subgroup.stabilizerInclusion' is declared both by the vendored commit-5a01f5fe
  TauCeti/GroupTheory/GroupAction/Stabilizer.lean and the vendored commit-97a5b235
  TauCeti/GroupTheory/GroupAction/Stabilizer/Basic.lean; neither is in T40's closure (pre-existing,
  outside this task's edit scope).
- 18:23 Pairwise test (scratch/t40-clash/pairwise.sh): `import T40` + `import M` for each of the 73
  other top-level Contrib modules M, compiled one after another: 73/73 OK
  (scratch/t40-clash/pairwise-result.txt). Eight of these M contain GroupWithZero.Units.Basic in their
  closure and so clashed with T40 before the fix: KroneckerWeber.Leaves, LocalKW.T30, T14.WP3,
  TYZGenus.ShimuraFricke, TauCeti GaloisCohomology.Congr, Global.Kummer.AuxiliaryPlaces,
  Global.Kummer.Norm, Global.PrescribedInvariant.
