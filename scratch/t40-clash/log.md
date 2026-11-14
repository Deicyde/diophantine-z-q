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
