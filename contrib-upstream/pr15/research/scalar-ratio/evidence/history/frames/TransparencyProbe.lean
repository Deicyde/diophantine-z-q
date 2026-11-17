import Research.DerivativeSwitch.Coordinate
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.FinCases

set_option backward.isDefEq.respectTransparency false

/-!
# The common-strict coordinate formula

Received as an uncompiled candidate. Current verification is recorded in
`research/scalar-ratio/VERIFICATION.md`.

The inputs are the original common-strict matrices, actual cycles and closed
rows. The output proves the cofactor coordinate identities. Invertibility of
`target D0 a b` is a generic boundary-independence hypothesis; it is not the
unit-ratio conclusion. Neither the strict determinant nor either source
frame is required to be a unit in the integral DVR.

Swapping the two target columns reduces BOTH sides to the same diagonal
normal differential. This avoids positing a map between the two complexes.
-/

namespace Research.DerivativeSwitch.ScalarRatio

open Matrix
open scoped Matrix

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

abbrev Index (I : Type*) := I ⊕ Fin 2
abbrev Local (K : Type*) := Fin 2 → K

/-- Concatenation of the common strict columns and the local two columns. -/
def join (D0 : Matrix (Index I) I K) (A : Matrix (Index I) (Fin 2) K) :
    Matrix (Index I) (Index I) K := fun i => Sum.elim (D0 i) (A i)

def pairCols (v x : Local K) : Matrix (Fin 2) (Fin 2) K :=
  !![v 0, x 0; v 1, x 1]

def area (v x : Local K) : K := v 0 * x 1 - v 1 * x 0

def cycle (h : I → K) (v : Local K) : Index I → K := Sum.elim h v

/-- Actual cycle in the penultimate column; fractional complement last. -/
def frame (h : I → K) (v x : Local K) : Matrix (Index I) (Index I) K :=
  Matrix.fromBlocks (1 : Matrix I I K) (fun i => ![h i, 0]) 0 (pairCols v x)

def target (D0 : Matrix (Index I) I K) (a b : Index I → K) :
    Matrix (Index I) (Index I) K :=
  join D0 (fun i => ![a i, b i])

set_option backward.isDefEq.respectTransparency false in
lemma frame_det (h : I → K) (v x : Local K) :
    (frame h v x).det = area v x := by
  rw [frame, Matrix.det_fromBlocks_zero₂₁]
  simp [pairCols, area, Matrix.det_fin_two, mul_comm]

lemma frame_cycle (h : I → K) (v x : Local K) :
    frame h v x *ᵥ Pi.single (Sum.inr (0 : Fin 2)) 1 = cycle h v := by
  ext i
  rcases i with i | i
  · simp [frame, Matrix.fromBlocks, cycle, Matrix.mulVec, dotProduct, Pi.single_apply]
  · fin_cases i <;> simp [frame, Matrix.fromBlocks, pairCols, cycle, Matrix.mulVec, dotProduct,
      Pi.single_apply]

lemma pairCols_action (J : Matrix (Fin 2) (Fin 2) K) (v x : Local K) :
    pairCols (J *ᵥ v) (J *ᵥ x) = J * pairCols v x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairCols, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma area_action (J : Matrix (Fin 2) (Fin 2) K) (v x : Local K) :
    area (J *ᵥ v) (J *ᵥ x) = J.det * area v x := by
  have h := congrArg Matrix.det (pairCols_action J v x)
  simpa [pairCols, area, Matrix.det_fin_two, Matrix.det_mul, mul_comm] using h

/-- The sole sign in the comparison is an actual column transposition. -/
lemma target_swap_det (D0 : Matrix (Index I) I K) (a b : Index I → K) :
    (target D0 b a).det = -(target D0 a b).det := by
  classical
  let k : Index I := Sum.inr 0
  let l : Index I := Sum.inr 1
  have hkl : k ≠ l := by simp [k, l]
  have heq : target D0 b a =
      (target D0 a b).submatrix id (Equiv.swap k l) := by
    ext i j
    rcases j with j | j
    · simp [target, join, Matrix.submatrix, k, l, Equiv.swap_apply_def]
    · fin_cases j <;>
        simp [target, join, Matrix.submatrix, k, l, Equiv.swap_apply_def]
  rw [heq, Matrix.det_permute']
  simp [Equiv.Perm.sign_swap hkl]

/-- The single-plane raw basis calculation. This is a matrix identity, not
an assumed equality of determinant coordinates. -/
lemma raw_frame_identity
    (D0 : Matrix (Index I) I K) (A : Matrix (Index I) (Fin 2) K)
    (h : I → K) (v x : Local K) (y : Index I → K)
    (hcycle : join D0 A *ᵥ cycle h v = 0) :
    join D0 A * frame h v x =
      target D0 y (A *ᵥ x) * normal (Sum.inr (0 : Fin 2)) := by
  classical
  have hc (i : Index I) :
      (∑ j : I, D0 i j * h j) + (A i 0 * v 0 + A i 1 * v 1) = 0 := by
    simpa [Matrix.mulVec, dotProduct, join, cycle, Fintype.sum_sum_type,
      Fin.sum_univ_two] using congrFun hcycle i
  ext i j
  rcases j with j | j
  · simp [Matrix.mul_apply, frame, Matrix.fromBlocks, join, target, normal, pairCols,
      Matrix.diagonal_apply, Matrix.one_apply, Fintype.sum_sum_type,
      mul_ite]
  · fin_cases j
    · simpa [Matrix.mul_apply, frame, Matrix.fromBlocks, join, target, normal, pairCols,
        Matrix.diagonal_apply, Matrix.one_apply, Fintype.sum_sum_type,
        Fin.sum_univ_two, mul_ite] using hc i
    · simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, frame, Matrix.fromBlocks, join, target,
        normal, pairCols, Matrix.diagonal_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two, mul_ite]

noncomputable def matrixUnit {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hM : M.det ≠ 0) : (Matrix n n K)ˣ :=
  ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hM)).unit

@[simp] lemma matrixUnit_val {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hM : M.det ≠ 0) :
    (matrixUnit M hM : Matrix n n K) = M :=
  IsUnit.unit_spec _

lemma raw_side_adjugate_ne_zero
    (D0 : Matrix (Index I) I K) (A : Matrix (Index I) (Fin 2) K)
    (h : I → K) (v x : Local K) (y : Index I → K)
    (hcycle : join D0 A *ᵥ cycle h v = 0)
    (harea : area v x ≠ 0)
    (htarget : (target D0 y (A *ᵥ x)).det ≠ 0) :
    (join D0 A).adjugate ≠ 0 := by
  let B := matrixUnit (frame h v x) (by simpa [frame_det] using harea)
  let T := matrixUnit (target D0 y (A *ᵥ x)) htarget
  apply adjugate_ne_zero_of_frame (join D0 A) B T (Sum.inr (0 : Fin 2))
  simpa [B, T] using raw_frame_identity D0 A h v x y hcycle

/-- Coordinate of an actual cycle/functional in one common-strict plane.
The other plane supplies `y`; its functional is not used or normalized here. -/
theorem raw_side_coordinate
    (D0 : Matrix (Index I) I K) (A : Matrix (Index I) (Fin 2) K)
    (h : I → K) (v x : Local K) (y lam : Index I → K)
    (hcycle : join D0 A *ᵥ cycle h v = 0)
    (hclosed : lam ᵥ* join D0 A = 0)
    (harea : area v x ≠ 0)
    (htarget : (target D0 y (A *ᵥ x)).det ≠ 0) :
    HasCoordinate (join D0 A) (cycle h v) lam
      (area v x * (lam ⬝ᵥ y) / (target D0 y (A *ᵥ x)).det) := by
  let B := matrixUnit (frame h v x) (by simpa [frame_det] using harea)
  let T := matrixUnit (target D0 y (A *ᵥ x)) htarget
  have hB : (B : Matrix (Index I) (Index I) K) = frame h v x := by
    simp [B]
  have hT : (T : Matrix (Index I) (Index I) K) = target D0 y (A *ᵥ x) := by
    simp [T]
  have hD : join D0 A * (B : Matrix (Index I) (Index I) K) =
      (T : Matrix (Index I) (Index I) K) * normal (Sum.inr (0 : Fin 2)) := by
    rw [hB, hT]
    exact raw_frame_identity D0 A h v x y hcycle
  have hz : cycle h v =
      (B : Matrix (Index I) (Index I) K) *ᵥ Pi.single (Sum.inr (0 : Fin 2)) 1 := by
    rw [hB, frame_cycle]
  have hc := coordinate_of_closed_frame (join D0 A) B T (cycle h v) lam
    (Sum.inr (0 : Fin 2)) hD hz hclosed
  have hq : (lam ᵥ* target D0 y (A *ᵥ x)) (Sum.inr (0 : Fin 2)) = lam ⬝ᵥ y := rfl
  rw [hB, hT, frame_det, hq] at hc
  convert hc using 1; ring

/-- The common-strict determinant formula, in arbitrary finite size.
Only the actual cycle equations, closedness, nonzero local area and independent
generic target directions are assumed. The scalar-ratio conclusion is derived. -/
set_option maxHeartbeats 1000000 in
theorem common_strict_coordinate_formula
    (D0 : Matrix (Index I) I K)
    (AF AS : Matrix (Index I) (Fin 2) K)
    (hF hS : I → K) (v x : Local K)
    (J : (Matrix (Fin 2) (Fin 2) K)ˣ)
    (lamF lamS : Index I → K)
    (hcycleF : join D0 AF *ᵥ cycle hF v = 0)
    (hcycleS : join D0 AS *ᵥ cycle hS ((J : Matrix _ _ K) *ᵥ v) = 0)
    (hclosedF : lamF ᵥ* join D0 AF = 0)
    (hclosedS : lamS ᵥ* join D0 AS = 0)
    (harea : area v x ≠ 0)
    (htarget : (target D0 (AF *ᵥ x) (AS *ᵥ ((J : Matrix _ _ K) *ᵥ x))).det ≠ 0) :
    let eta := area v x
    let delta := (J : Matrix (Fin 2) (Fin 2) K).det
    let a := AF *ᵥ x
    let b := AS *ᵥ ((J : Matrix (Fin 2) (Fin 2) K) *ᵥ x)
    let theta := (target D0 a b).det
    let qF := lamF ⬝ᵥ b
    let qS := lamS ⬝ᵥ a
    HasCoordinate (join D0 AF) (cycle hF v) lamF (-eta * qF / theta) ∧
    HasCoordinate (join D0 AS) (cycle hS ((J : Matrix _ _ K) *ᵥ v)) lamS
      (delta * eta * qS / theta) := by
  dsimp only
  constructor
  · have ht : (target D0 (AS *ᵥ ((J : Matrix _ _ K) *ᵥ x)) (AF *ᵥ x)).det ≠ 0 := by
      rw [target_swap_det]
      exact neg_ne_zero.mpr htarget
    have hf := raw_side_coordinate (K := K) (I := I) D0 AF hF v x
      (AS *ᵥ ((J : Matrix _ _ K) *ᵥ x)) lamF hcycleF hclosedF harea ht
    rw [target_swap_det] at hf
    simpa only [div_neg, neg_mul, neg_div] using hf
  · have hj : (J : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
      (Matrix.isUnits_det_units J).ne_zero
    have ha : area ((J : Matrix _ _ K) *ᵥ v) ((J : Matrix _ _ K) *ᵥ x) ≠ 0 := by
      rw [area_action]
      exact mul_ne_zero hj harea
    have hs := raw_side_coordinate (K := K) (I := I) D0 AS hS ((J : Matrix _ _ K) *ᵥ v)
      ((J : Matrix _ _ K) *ᵥ x) (AF *ᵥ x) lamS hcycleS hclosedS ha htarget
    rw [area_action] at hs
    exact hs

/-- All source-bearing inputs, with no determinant-coordinate or unit-ratio
hypothesis. The arithmetic consumer must supply these *actual* rows/vectors. -/
structure CommonStrictData (K I : Type*) [Field K] [Fintype I] [DecidableEq I] where
  D0 : Matrix (Index I) I K
  AF : Matrix (Index I) (Fin 2) K
  AS : Matrix (Index I) (Fin 2) K
  hF : I → K
  hS : I → K
  v : Local K
  x : Local K
  J : (Matrix (Fin 2) (Fin 2) K)ˣ
  lamF : Index I → K
  lamS : Index I → K
  cycleF : join D0 AF *ᵥ cycle hF v = 0
  cycleS : join D0 AS *ᵥ cycle hS ((J : Matrix _ _ K) *ᵥ v) = 0
  closedF : lamF ᵥ* join D0 AF = 0
  closedS : lamS ᵥ* join D0 AS = 0
  area_ne : area v x ≠ 0
  target_ne : (target D0 (AF *ᵥ x) (AS *ᵥ ((J : Matrix _ _ K) *ᵥ x))).det ≠ 0

namespace CommonStrictData

variable (d : CommonStrictData K I)

def delta : K := (d.J : Matrix (Fin 2) (Fin 2) K).det
def eta : K := area d.v d.x
def a : Index I → K := d.AF *ᵥ d.x
def b : Index I → K := d.AS *ᵥ ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.x)
def theta : K := (target d.D0 d.a d.b).det
def qF : K := d.lamF ⬝ᵥ d.b
def qS : K := d.lamS ⬝ᵥ d.a

theorem delta_ne_zero : d.delta ≠ 0 := (Matrix.isUnits_det_units d.J).ne_zero

set_option maxHeartbeats 1000000 in
theorem coordinate_values (uF uS : K)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix _ _ K) *ᵥ d.v)) d.lamS uS) :
    uF = -d.eta * d.qF / d.theta ∧
    uS = d.delta * d.eta * d.qS / d.theta := by
  have hcoords := common_strict_coordinate_formula (K := K) (I := I) d.D0 d.AF d.AS d.hF d.hS
    d.v d.x d.J d.lamF d.lamS d.cycleF d.cycleS d.closedF d.closedS
    d.area_ne d.target_ne
  dsimp only at hcoords
  have htF : (target d.D0 d.b d.a).det ≠ 0 := by
    rw [target_swap_det]
    exact neg_ne_zero.mpr d.target_ne
  have hadjF := raw_side_adjugate_ne_zero (K := K) (I := I) d.D0 d.AF d.hF d.v d.x d.b
    d.cycleF d.area_ne htF
  have hareaS : area ((d.J : Matrix _ _ K) *ᵥ d.v)
      ((d.J : Matrix _ _ K) *ᵥ d.x) ≠ 0 := by
    rw [area_action]
    exact mul_ne_zero d.delta_ne_zero d.area_ne
  have hadjS := raw_side_adjugate_ne_zero (K := K) (I := I) d.D0 d.AS d.hS
    ((d.J : Matrix _ _ K) *ᵥ d.v) ((d.J : Matrix _ _ K) *ᵥ d.x) d.a
    d.cycleS hareaS d.target_ne
  constructor
  · exact coordinate_unique _ _ _ _ _ hadjF huF hcoords.1
  · exact coordinate_unique _ _ _ _ _ hadjS huS hcoords.2

end CommonStrictData

end Research.DerivativeSwitch.ScalarRatio
