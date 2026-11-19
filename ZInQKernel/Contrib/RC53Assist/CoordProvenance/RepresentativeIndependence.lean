import ZInQKernel.Contrib.RC53Assist.CoordLink.Comparison
import ZInQKernel.Contrib.RC53Assist.CoordLink.Patterns

/-!
# Coordinates depend on the same cohomology class and functional

Changing the representative of a class by a boundary, or a closed functional
by a dual boundary, is an elementary graded basis shear of the augmented
complex.  Its determinant is one.  The retained coordinate is therefore
unchanged, including at zero coordinates and acyclic constituents.

This is the representative-independence needed by Definition
ex:arith-coordinate, TeX 3877–3892, and by the retained transport in
ex:limits-fixed-field-clearing, TeX 5509–5516.  No additional printed
proposition or exactness of the augmented complex is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance

open Matrix
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.CoordLink (kmCoord_eq_of_fourMap_retained_total)

section Four

variable {K : Type*} [Field K]
  {ι0 ι1 ι2 ι3 : Type*}
  [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  (C : FourCx K ι0 ι1 ι2 ι3) (z : ι1 → K) (lam : ι2 → K)
  (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0)

/-- The elementary shear adding a class boundary to the augmentation column. -/
def classBoundaryShear (b : ι0 → K) : GradedBasisChange (C.aug z lam hz hlam).toBased where
  Pe := fromBlocks (fromBlocks 1 (-replicateCol Unit b) 0 1) 0 0 1
  Qe := fromBlocks (fromBlocks 1 (replicateCol Unit b) 0 1) 0 0 1
  Po := 1
  Qo := 1
  hPQe := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp
  hPQo := Matrix.one_mul _
  deg_Pe := by
    rintro ((i | i) | i) ((j | j) | j) h
    all_goals first | rfl | exact absurd rfl h
  deg_Qe := by
    rintro ((i | i) | i) ((j | j) | j) h
    all_goals first | rfl | exact absurd rfl h
  deg_Po := hasDeg_one _
  deg_Qo := hasDeg_one _

/-- The augmentation-column shear has determinant one. -/
theorem classBoundaryShear_det (b : ι0 → K) :
    (classBoundaryShear C z lam hz hlam b).Qe.det = 1 := by
  change (fromBlocks (fromBlocks (1 : Matrix ι0 ι0 K) (replicateCol Unit b) 0 1) 0 0 1).det = 1
  rw [det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]
  simp

/-- Adding a boundary is exactly the indicated graded shear of the augmented complex. -/
theorem classBoundaryShear_rebase (b : ι0 → K)
    (hz' : C.d1 *ᵥ (z + C.d0 *ᵥ b) = 0) :
    (C.aug (z + C.d0 *ᵥ b) lam hz' hlam).toBased =
      (C.aug z lam hz hlam).toBased.rebase (classBoundaryShear C z lam hz hlam b) := by
  have hcol : fromCols C.d0 (replicateCol Unit z) *
      fromBlocks (1 : Matrix ι0 ι0 K) (replicateCol Unit b) 0 1 =
      fromCols C.d0 (replicateCol Unit (z + C.d0 *ᵥ b)) := by
    erw [fromCols_mul_fromBlocks]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
    congr 1
    ext i q
    cases q
    simp only [Matrix.add_apply, mul_apply, replicateCol_apply, Pi.add_apply, mulVec, dotProduct]
    ring
  apply BasedCx.ext'
  · rfl
  · rfl
  · change fromBlocks (fromCols C.d0 (replicateCol Unit (z + C.d0 *ᵥ b))) 0 0
        (fromRows C.d2 (replicateRow Unit lam)) =
      1 * fromBlocks (fromCols C.d0 (replicateCol Unit z)) 0 0
        (fromRows C.d2 (replicateRow Unit lam)) *
          fromBlocks (fromBlocks 1 (replicateCol Unit b) 0 1) 0 0 1
    rw [Matrix.one_mul, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, zero_add, add_zero]
    erw [hcol]
  · change fromBlocks 0 0 C.d1 0 =
      fromBlocks (fromBlocks 1 (-replicateCol Unit b) 0 1) 0 0 1 * fromBlocks 0 0 C.d1 0 * 1
    rw [Matrix.mul_one, fromBlocks_multiply]
    simp

/-- The retained coordinate is unchanged when the class representative changes by a boundary. -/
theorem kmCoord_class_boundary (b : ι0 → K)
    (hz' : C.d1 *ᵥ (z + C.d0 *ᵥ b) = 0)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C (z + C.d0 *ᵥ b) lam hz' hlam σ = kmCoord C z lam hz hlam σ := by
  unfold kmCoord
  rw [classBoundaryShear_rebase C z lam hz hlam b hz', torsion_rebase',
    classBoundaryShear_det]
  simp only [classBoundaryShear, det_one, one_mul, mul_one]

/-- The elementary shear adding a dual boundary to the augmentation row. -/
def functionalBoundaryShear (r : ι3 → K) : GradedBasisChange (C.aug z lam hz hlam).toBased where
  Pe := 1
  Qe := 1
  Po := fromBlocks 1 0 0 (fromBlocks 1 0 (replicateRow Unit r) 1)
  Qo := fromBlocks 1 0 0 (fromBlocks 1 0 (-replicateRow Unit r) 1)
  hPQe := Matrix.one_mul _
  hPQo := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp
  deg_Pe := hasDeg_one _
  deg_Qe := hasDeg_one _
  deg_Po := by
    rintro (i | (i | i)) (j | (j | j)) h
    all_goals first | rfl | exact absurd rfl h
  deg_Qo := by
    rintro (i | (i | i)) (j | (j | j)) h
    all_goals first | rfl | exact absurd rfl h

/-- The augmentation-row shear has determinant one. -/
theorem functionalBoundaryShear_det (r : ι3 → K) :
    (functionalBoundaryShear C z lam hz hlam r).Po.det = 1 := by
  change (fromBlocks 1 0 0 (fromBlocks (1 : Matrix ι3 ι3 K) 0 (replicateRow Unit r) 1)).det = 1
  rw [det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂]
  simp

/-- Adding a dual boundary is exactly the indicated graded shear. -/
theorem functionalBoundaryShear_rebase (r : ι3 → K)
    (hlam' : (lam + r ᵥ* C.d2) ᵥ* C.d1 = 0) :
    (C.aug z (lam + r ᵥ* C.d2) hz hlam').toBased =
      (C.aug z lam hz hlam).toBased.rebase (functionalBoundaryShear C z lam hz hlam r) := by
  have hrow : fromBlocks (1 : Matrix ι3 ι3 K) 0 (replicateRow Unit r) 1 *
      fromRows C.d2 (replicateRow Unit lam) =
      fromRows C.d2 (replicateRow Unit (lam + r ᵥ* C.d2)) := by
    erw [fromBlocks_mul_fromRows]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero]
    congr 1
    ext q j
    cases q
    simp only [Matrix.add_apply, mul_apply, replicateRow_apply, Pi.add_apply, vecMul, dotProduct]
    ring
  apply BasedCx.ext'
  · rfl
  · rfl
  · change fromBlocks (fromCols C.d0 (replicateCol Unit z)) 0 0
        (fromRows C.d2 (replicateRow Unit (lam + r ᵥ* C.d2))) =
      fromBlocks 1 0 0 (fromBlocks 1 0 (replicateRow Unit r) 1) *
        fromBlocks (fromCols C.d0 (replicateCol Unit z)) 0 0
          (fromRows C.d2 (replicateRow Unit lam)) * 1
    rw [Matrix.mul_one, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero]
    erw [hrow]
  · change fromBlocks 0 0 C.d1 0 =
      1 * fromBlocks 0 0 C.d1 0 *
        fromBlocks 1 0 0 (fromBlocks 1 0 (-replicateRow Unit r) 1)
    rw [Matrix.one_mul, fromBlocks_multiply]
    simp

/-- The retained coordinate is unchanged when the functional changes by a dual boundary. -/
theorem kmCoord_functional_boundary (r : ι3 → K)
    (hlam' : (lam + r ᵥ* C.d2) ᵥ* C.d1 = 0)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C z (lam + r ᵥ* C.d2) hz hlam' σ = kmCoord C z lam hz hlam σ := by
  unfold kmCoord
  rw [functionalBoundaryShear_rebase C z lam hz hlam r hlam', torsion_rebase',
    functionalBoundaryShear_det]
  simp only [functionalBoundaryShear, det_one, one_mul, mul_one]

end Four

section BoundaryComparison

variable {K : Type*} [Field K]
  {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type*}
  [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']

omit [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
/-- A boundary may be added to a cycle without changing closedness. -/
theorem classBoundaryCycle (C : FourCx K ι0 ι1 ι2 ι3) (z : ι1 → K)
    (hz : C.d1 *ᵥ z = 0) (b : ι0 → K) : C.d1 *ᵥ (z + C.d0 *ᵥ b) = 0 := by
  rw [mulVec_add, mulVec_mulVec, C.d10, zero_mulVec, hz, add_zero]

omit [Fintype ι0] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
/-- A dual boundary may be added to a functional without changing closedness. -/
theorem functionalBoundaryClosed (C : FourCx K ι0 ι1 ι2 ι3) (lam : ι2 → K)
    (hlam : lam ᵥ* C.d1 = 0) (r : ι3 → K) : (lam + r ᵥ* C.d2) ᵥ* C.d1 = 0 := by
  rw [add_vecMul, vecMul_vecMul, C.d21, vecMul_zero, hlam, add_zero]

/-- A retained comparison need only carry the same cohomology classes.
Its class discrepancy and functional discrepancy may be retained boundaries.
The conclusion includes zero and acyclic coordinates. -/
theorem kmCoord_retained_cohomology_comparison
    {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'} (F : FourMap C D)
    (zC : ι1 → K) (lC : ι2 → K) (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (zD : ι1' → K) (lD : ι2' → K) (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (bD : ι0' → K) (rC : ι3 → K)
    (hclass : F.f1 *ᵥ zC = zD + D.d0 *ᵥ bD)
    (hfun : lD ᵥ* F.f2 = lC + rC ᵥ* C.d2)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit))
    (hcone : torsion (BasedCx.cone (F.augMap zC (lC + rC ᵥ* C.d2) hzC
        (functionalBoundaryClosed C lC hlC rC) (zD + D.d0 *ᵥ bD) lD
        (classBoundaryCycle D zD hzD bD) hlD hclass hfun)) (σD.sumCongr σC.symm) =
      (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit))) :
    kmCoord C zC lC hzC hlC σC = kmCoord D zD lD hzD hlD σD := by
  calc
    kmCoord C zC lC hzC hlC σC =
        kmCoord C zC (lC + rC ᵥ* C.d2) hzC (functionalBoundaryClosed C lC hlC rC) σC :=
      (kmCoord_functional_boundary C zC lC hzC hlC rC _ σC).symm
    _ = kmCoord D (zD + D.d0 *ᵥ bD) lD (classBoundaryCycle D zD hzD bD) hlD σD :=
      kmCoord_eq_of_fourMap_retained_total F zC (lC + rC ᵥ* C.d2) hzC
        (functionalBoundaryClosed C lC hlC rC) (zD + D.d0 *ᵥ bD) lD
        (classBoundaryCycle D zD hzD bD) hlD hclass hfun σC σD hcone
    _ = kmCoord D zD lD hzD hlD σD := kmCoord_class_boundary D zD lD hzD hlD bD _ σD

end BoundaryComparison

end ZInQ.Contrib.RC53Assist.CoordProvenance
