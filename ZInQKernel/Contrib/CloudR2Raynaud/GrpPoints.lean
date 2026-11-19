import ZInQKernel.Contrib.CloudR2Raynaud.GenericPoints

/-!
# Literal full-universe PkgI2/Grp point base-change API

H4 round 2. Thin export of the already-proved GenericPoints adjunction/Spec
maps directly on the ORIGINAL PkgI2 group objects. Intended for the H5
supplied-model/counting join, without copying or re-proving point transport.
Both sides retain the same group data definitionally; no replacement object,
field, or Galois action is used.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace ZInQ.Contrib.CloudR2Raynaud.GrpPoints

open ZInQ.Contrib.CloudR2Raynaud.GenericPoints

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
    (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A]
    (Ω : Type u) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

/-- The original fixed base change, INCLUDING its group object data. -/
theorem baseChange_with_group_data :
    Grp.mk (GenericPoints.baseChange (ofFixedGrp A) L).X = PkgI2.baseChange A L := rfl

/-- Genuine original-group point bijection over the SAME Ω. -/
def bcPts : PkgI2.Pts (PkgI2.baseChange A L) Ω ≃* PkgI2.Pts A Ω :=
  GenericPoints.bcPt (ofFixedGrp A) Ω

/-- Literal original galAct/scalar-restriction naturality, at arbitrary universe. -/
theorem bcPts_galAct (σ : Ω ≃ₐ[L] Ω) (p : PkgI2.Pts (PkgI2.baseChange A L) Ω) :
    bcPts A Ω (PkgI2.galAct (PkgI2.baseChange A L) σ p) =
      PkgI2.galAct A (σ.restrictScalars K) (bcPts A Ω p) :=
  GenericPoints.bcPt_galAct (ofFixedGrp A) Ω σ p

/-- Every actual original torsion order, including0, is preserved by this map. -/
theorem bcPts_pow (p : PkgI2.Pts (PkgI2.baseChange A L) Ω) (m : ℕ) :
    bcPts A Ω (p ^ m) = (bcPts A Ω p) ^ m := map_pow _ _ _

/-- GenericFields factory keeps the actual original PkgI2 point action. -/
theorem original_galAct (σ : Ω ≃ₐ[K] Ω) (x : PkgI2.Pts A Ω) :
    PkgI2.galAct A σ x = (ofFixedGrp A).galAct σ x := rfl

end ZInQ.Contrib.CloudR2Raynaud.GrpPoints
