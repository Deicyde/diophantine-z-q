import ZInQKernel.Contrib.CloudB3RC53.StageCone.Comparison

/-!
# A nonunit strict disk is visible to individual comparisons

This is an algebraic obstruction, not a claimed arithmetic Selmer example.
Over any coefficient ring embedded in a field, append the same nonzero disk
with differential `a` in degrees one and two to the two plane models. Their
coordinates acquire the common factor `a⁻¹`. Every generic comparison to the
bare plane has cone torsion `a`, so the individual unit condition holds
exactly when `a` is an integral unit. Nevertheless the existing coordinate
step is realized with the original plane pairing and strict volume `a`.
-/

noncomputable section
set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.StageCone.Obstruction

open Matrix Module
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.StageCone
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.Central
open ZInQ.Manuscript.RC.Uniform

variable {A F : Type} [CommRing A] [Field F] (ι : A →+* F) (a : A) (ha : ι a ≠ 0)

def planeVector : Fin 2 → F := ![1, 0]

theorem planeVector_ne_zero : (planeVector : Fin 2 → F) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [planeVector] at this

theorem switchedVector : switchJ0 F *ᵥ (planeVector : Fin 2 → F) = planeVector := by
  ext i
  fin_cases i <;> simp [switchJ0, planeVector, mulVec, dotProduct, Fin.sum_univ_two]

def oldMatrix : Matrix (Fin 3) (Fin 3) A := !![0, 0, 0; 0, -1, 0; 0, 0, a]

def newMatrix : Matrix (Fin 3) (Fin 3) A := !![0, -1, 0; 0, 0, 0; 0, 0, a]

def oldStage : TwoTermStage ι where
  n := 2
  D := oldMatrix a
  z := ![1, 0, 0]
  w := ![1, 0, 0]
  u := -(ι a)⁻¹
  hz := by ext i; fin_cases i <;> simp [oldMatrix, mulVec, dotProduct, Fin.sum_univ_three]
  hw := by ext j; fin_cases j <;> simp [oldMatrix, vecMul, dotProduct, Fin.sum_univ_three]
  hu := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [oldMatrix, adjugate_fin_three, vecMulVec_apply, ha]

def newStage : TwoTermStage ι where
  n := 2
  D := newMatrix a
  z := ![1, 0, 0]
  w := ![0, 1, 0]
  u := (ι a)⁻¹
  hz := by ext i; fin_cases i <;> simp [newMatrix, mulVec, dotProduct, Fin.sum_univ_three]
  hw := by ext j; fin_cases j <;> simp [newMatrix, vecMul, dotProduct, Fin.sum_univ_three]
  hu := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [newMatrix, adjugate_fin_three, vecMulVec_apply, ha]

theorem oldStage_ne_zero : (oldStage ι a ha).u ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ha)

theorem newStage_ne_zero : (newStage ι a ha).u ≠ 0 := inv_ne_zero ha

theorem oldStage_adjugate : ((oldStage ι a ha).D.map ι).adjugate ≠ 0 := by
  intro h
  have he := congrFun (congrFun h 0) 0
  change ((oldMatrix a).map ι).adjugate (0 : Fin 3) 0 = 0 at he
  rw [adjugate_fin_three] at he
  simp [oldMatrix, ha] at he

theorem newStage_adjugate : ((newStage ι a ha).D.map ι).adjugate ≠ 0 := by
  intro h
  have he := congrFun (congrFun h 0) 1
  change ((newMatrix a).map ι).adjugate (0 : Fin 3) 1 = 0 at he
  rw [adjugate_fin_three] at he
  simp [newMatrix, ha] at he

theorem oldStage_sign : stageSign (oldStage ι a ha) = 1 := by
  norm_num [stageSign, oldStage]

theorem newStage_sign : stageSign (newStage ι a ha) = 1 := by
  norm_num [stageSign, newStage]

/-- A generic comparison using one primitive class coordinate and one primitive target row. -/
def primitiveComparison (S : TwoTermStage ι) (M : Matrix (Fin 2) (Fin 2) F)
    (z l : Fin 2 → F) (hz : M *ᵥ z = 0) (i : Fin (S.n + 1)) (j : Fin 2)
    (hi : ι (S.z i) = 1) (hj : l j = 1) : StageMap S M z l where
  f :=
    { f0 := 0
      f1 := vecMulVec z (Pi.single i 1)
      f2 := vecMulVec (Pi.single j 1) (fun k => ι (S.w k))
      f3 := 0
      c0 := Matrix.ext fun _ k => k.elim
      c1 := by
        change M * vecMulVec z (Pi.single i 1) =
          vecMulVec (Pi.single j 1) (fun k => ι (S.w k)) * S.D.map ι
        have hw : (fun k => ι (S.w k)) ᵥ* S.D.map ι = 0 := stage_hw S
        rw [mul_vecMulVec, vecMulVec_mul, hz, hw]
        simp [vecMulVec]
      c2 := Matrix.ext fun k _ => k.elim }
  hz := by
    ext k
    have hr : (Pi.single i (1 : F) : Fin (S.n + 1) → F) ⬝ᵥ
        (fun t => ι (S.z t)) = 1 := by simp [hi]
    simp only [mulVec, dotProduct, vecMulVec_apply]
    calc
      (∑ t, z k * (Pi.single i (1 : F) : Fin (S.n + 1) → F) t * ι (S.z t)) =
          z k * ((Pi.single i (1 : F) : Fin (S.n + 1) → F) ⬝ᵥ
            (fun t => ι (S.z t))) := by
              simp only [dotProduct, Finset.mul_sum, mul_assoc]
      _ = z k := by rw [hr, mul_one]
  hl := by
    ext k
    have hr : l ⬝ᵥ (Pi.single j (1 : F) : Fin 2 → F) = 1 := by simp [hj]
    simp only [vecMul, dotProduct, vecMulVec_apply]
    calc
      (∑ t, l t * ((Pi.single j (1 : F) : Fin 2 → F) t * ι (S.w k))) =
          (l ⬝ᵥ (Pi.single j (1 : F) : Fin 2 → F)) * ι (S.w k) := by
            simp only [dotProduct, Finset.sum_mul, mul_assoc]
      _ = ι (S.w k) := by rw [hr, one_mul]

/-- A nonempty generic comparison for the old stage. -/
def oldComparison : StageMap (oldStage ι a ha) (oldMat 1 planeVector) planeVector (Pi.single 0 1) :=
  primitiveComparison ι (oldStage ι a ha) (oldMat 1 planeVector) planeVector (Pi.single 0 1)
    (oldMat_hz 1 planeVector) 0 0 (by simp [oldStage]) (by simp)

/-- A nonempty generic comparison for the new stage. -/
def newComparison : StageMap (newStage ι a ha) (newMat 1 1 (switchJ0 F) planeVector)
    (switchJ0 F *ᵥ planeVector) (Pi.single 1 1) :=
  primitiveComparison ι (newStage ι a ha) (newMat 1 1 (switchJ0 F) planeVector)
    (switchJ0 F *ᵥ planeVector) (Pi.single 1 1) (newMat_hz 1 1 (switchJ0 F) planeVector)
    0 1 (by simp [newStage]) (by simp)

/-- The strict disk contributes `a` to every old comparison cone. -/
theorem oldComparison_torsion
    (g : StageMap (oldStage ι a ha) (oldMat 1 planeVector) planeVector (Pi.single 0 1)) :
    g.coneTorsion (oldMat_hz 1 planeVector) (oldMat_hl 1 planeVector) = ι a := by
  have hk := stage_coord_eq g (oldMat_hz 1 planeVector) (oldMat_hl 1 planeVector)
    (oldStage_ne_zero ι a ha) (oldStage_adjugate ι a ha)
    (oldMat_coord one_ne_zero planeVector) (by simp)
    (oldMat_adjugate_ne_zero one_ne_zero planeVector_ne_zero)
  have he : (ι a)⁻¹ * (-1) = stageSign (oldStage ι a ha) * (-1) *
      (g.coneTorsion (oldMat_hz 1 planeVector) (oldMat_hl 1 planeVector))⁻¹ := by
    simpa [oldStage] using hk
  have ht := solve_cone (stageSign_mul_self (oldStage ι a ha)) (by simp : (-1 : F) ≠ 0) he
  simpa [oldStage_sign] using ht

/-- The same strict disk contributes the same torsion on the new side. -/
theorem newComparison_torsion
    (g : StageMap (newStage ι a ha) (newMat 1 1 (switchJ0 F) planeVector)
      (switchJ0 F *ᵥ planeVector) (Pi.single 1 1)) :
    g.coneTorsion (newMat_hz 1 1 (switchJ0 F) planeVector)
      (newMat_hl 1 1 (switchJ0 F) planeVector) = ι a := by
  have hk := stage_coord_eq g (newMat_hz 1 1 (switchJ0 F) planeVector)
    (newMat_hl 1 1 (switchJ0 F) planeVector) (newStage_ne_zero ι a ha) (newStage_adjugate ι a ha)
    (newMat_coord one_ne_zero one_ne_zero (switchJ0 F) planeVector) (by simp)
    (newMat_adjugate_ne_zero one_ne_zero one_ne_zero
      (mulVec_ne_zero_of_sq (switchJ0_sq (K := F)) planeVector_ne_zero))
  have he : (ι a)⁻¹ * 1 = stageSign (newStage ι a ha) * 1 *
      (g.coneTorsion (newMat_hz 1 1 (switchJ0 F) planeVector)
        (newMat_hl 1 1 (switchJ0 F) planeVector))⁻¹ := by
    simpa [newStage] using hk
  have ht := solve_cone (stageSign_mul_self (newStage ι a ha)) one_ne_zero he
  simpa [newStage_sign] using ht

/-- Generic equivalence does not remove a nonunit integral strict determinant. -/
theorem oldIntegralUnit_iff (hι : Function.Injective ι)
    (g : StageMap (oldStage ι a ha) (oldMat 1 planeVector) planeVector (Pi.single 0 1)) :
    g.IntegralUnit (oldMat_hz 1 planeVector) (oldMat_hl 1 planeVector) ↔ IsUnit a := by
  change (∃ c : Aˣ, g.coneTorsion _ _ = stageSign (oldStage ι a ha) * ι c) ↔ IsUnit a
  simp only [oldComparison_torsion, oldStage_sign, _root_.one_mul]
  constructor
  · rintro ⟨c, hc⟩
    rw [hι hc]
    exact Units.isUnit c
  · rintro ⟨c, hc⟩
    exact ⟨c, congrArg ι hc.symm⟩

/-- The sharpened comparison can fail even though both integral stages have generic comparisons. -/
theorem not_stageConeComparison_of_nonunit (hι : Function.Injective ι) (hn : ¬ IsUnit a) :
    ¬ StageConeComparison (oldStage ι a ha) (newStage ι a ha) 1 1 (switchJ0 F) planeVector := by
  rintro ⟨⟨g, hg⟩, _⟩
  exact hn ((oldIntegralUnit_iff ι a ha hι g).1 hg)

/-- The coordinates still have the exact switch sign relation. -/
theorem coordinate_sign_relation : (oldStage ι a ha).u = -(newStage ι a ha).u := rfl

/-- The existing coordinate-step consumer remains realizable, with the original plane data.
Its strict volume is `a`, not a unit normalization. -/
def commonDiskCoordStep : CoordStep ι (oldStage ι a ha).u (newStage ι a ha).u := by
  let X₀ := planeSwitchData (ε := (1 : F)) (σ := (1 : F)) one_ne_zero (mul_one 1)
    (switchJ0_sq (K := F)) (switchJ0_det (K := F)) planeVector_ne_zero (-1) (-1)
  let X : SwitchCoordData F :=
    { X₀ with
      ω := ι a • X₀.ω
      hω := by intro x; change ι a * X₀.ω x x = 0; rw [X₀.hω x, mul_zero]
      hxw := by change ι a * X₀.ω _ _ ≠ 0; exact mul_ne_zero ha X₀.hxw
      hyw := by change ι a * X₀.ω _ _ ≠ 0; exact mul_ne_zero ha X₀.hyw }
  refine
    { X := X
      mF := -1
      mS := -1
      σ₀ := 1
      hmF := isUnit_one.neg
      hmS := isUnit_one.neg
      hμF := by change (-1 : F) = ι (-1 : A); simp
      hμS := by change (-1 : F) = ι (-1 : A); simp
      hσ₀ := by change (1 : F) = ι (1 : A); simp
      hu := ?_
      hu' := ?_ }
  · rw [SwitchCoordData.uF, coordF_eq (Pi.basisFun F (Fin 2)) X.hJ2 X.hfA X.hsA X.hsB X.hω
      X.μF X.hxw]
    change -(ι a)⁻¹ = (-1 : F) / (1 * (ι a * dualVol (Pi.basisFun F (Fin 2)) _ _))
    rw [dualVol_basis]
    simp [div_eq_mul_inv]
  · rw [SwitchCoordData.uS, coordS_eq (Pi.basisFun F (Fin 2)) X.hJ2 X.hJdet X.hfA X.hfB X.hsB X.hω
      X.μS X.hyw]
    change (ι a)⁻¹ = -(-1 : F) / (1 * (1 * (ι a * dualVol (Pi.basisFun F (Fin 2)) _ _)))
    rw [dualVol_basis]
    simp [div_eq_mul_inv]

set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs true

end ZInQ.Contrib.RC53Assist.StageCone.Obstruction
