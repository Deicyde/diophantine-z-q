/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D7.Defs
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_eq_refl_of_mapPt_eq_of_three_le

/-!
# W13 dictionary D7, step 2: rigidity of level-3 objects

`rigidInput`: over a ring in which `3` is a unit, an automorphism of a level-3 object that
preserves the group law, the action and the level point is the identity. This is the FLT theorem
`WithFullLevel.eq_refl_of_mapPt_eq_of_three_le` with `hB`, `hΛ` from `order_bridge` (`q = 2`,
`q' = 3`). Uniqueness of level pullbacks (`IsLevelPB.unique`, `Defs.lean`) follows from it.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D7

open CategoryTheory AlgebraicGeometry Limits
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj ZInQ.Contrib.CloudW03NeronSurj.FLT
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open ZInQ.Contrib.CloudW03NeronSurj.FLT.CerednikDrinfeld.QM
open ZInQ.Contrib.CloudB2Shimura.Dictionary

/-- `RigidInput`, proved from the FLT rigidity theorem. -/
theorem rigidInput : RigidInput := fun S _ h3 u e he hmul hact hP =>
  FakeEllipticCurve.WithFullLevel.eq_refl_of_mapPt_eq_of_three_le
    (q := 2) (q' := 3) (by norm_num) order_bridge.1 Λ order_bridge.2.1 (le_refl 3) h3 u
    e he hmul hact hP

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D7
