/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D7.Obligation

/-! # W13 D7 checks: exact obligation, the three discharged inputs, data of the glued family, axioms -/

open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.CloudB2Shimura.Dictionary ZInQ.Contrib.CloudB2Shimura.Dictionary.D7

example : D7_Obligation := d7_obligation

/-- The three inputs are actual theorems (no hypotheses). -/
example : BCInput := bcInput
example : RigidInput := rigidInput
example : DimInput := dimInput

/-- The glued family's data are literally the glued FLT data: the structure map is the relative
gluing `toBase`, `iota a` restricts on each chart to `act (toΛ a)`, and `eta a` restricts to
`a · P` (composed with `U ≅ Spec Γ(U)`). -/
example {M : Scheme.{0}} (F : LocalFamily M) : F.toQMFamily.F.hom = F.toBase := rfl
example {M : Scheme.{0}} (F : LocalFamily M) (a : LeafQM.O) : F.toQMFamily.iota a = F.iotaG a := rfl
example {M : Scheme.{0}} (F : LocalFamily M) (a : LeafQM.O) : F.toQMFamily.eta a = F.etaG a := rfl
example {M : Scheme.{0}} (F : LocalFamily M) (a : LeafQM.O) (U : M.affineOpens) :
    F.ι U ≫ F.iotaG a = F.iota a U ≫ F.ι U := F.ι_iotaG a U
example {M : Scheme.{0}} (F : LocalFamily M) (a : LeafQM.O) (U : M.affineOpens) :
    U.1.ι ≫ F.etaG a = F.sec a U ≫ F.ι U := F.ι_etaG a U
example {M : Scheme.{0}} (F : LocalFamily M) (U : M.affineOpens) :
    CategoryTheory.IsPullback (F.p U) (F.ι U) U.1.ι F.toBase := F.isPullback_ι U

#print axioms d7_obligation
#print axioms bcInput
#print axioms rigidInput
#print axioms dimInput
