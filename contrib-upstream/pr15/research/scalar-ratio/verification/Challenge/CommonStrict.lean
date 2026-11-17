import Challenge.Coordinate
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.FinCases

/-!
# The common-strict coordinate formula

Frozen concrete specification: selected theorem proof holes are intentional.
No solution module is imported. Reviewed against the intended mathematical contract.

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

noncomputable def matrixUnit {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hM : M.det ≠ 0) : (Matrix n n K)ˣ :=
  ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hM)).unit

theorem raw_side_coordinate
    (D0 : Matrix (Index I) I K) (A : Matrix (Index I) (Fin 2) K)
    (h : I → K) (v x : Local K) (y lam : Index I → K)
    (hcycle : join D0 A *ᵥ cycle h v = 0)
    (hclosed : lam ᵥ* join D0 A = 0)
    (harea : area v x ≠ 0)
    (htarget : (target D0 y (A *ᵥ x)).det ≠ 0) :
    HasCoordinate (join D0 A) (cycle h v) lam
      (area v x * (lam ⬝ᵥ y) / (target D0 y (A *ᵥ x)).det) := by sorry

theorem common_strict_coordinate_formula
    (D0 : Matrix (Index I) I K)
    (AF AS : Matrix (Index I) (Fin 2) K)
    (hF hS : I → K) (v x : Local K)
    (J : (Matrix (Fin 2) (Fin 2) K)ˣ)
    (lamF lamS : Index I → K)
    (hcycleF : join D0 AF *ᵥ cycle hF v = 0)
    (hcycleS : join D0 AS *ᵥ cycle hS ((J : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = 0)
    (hclosedF : lamF ᵥ* join D0 AF = 0)
    (hclosedS : lamS ᵥ* join D0 AS = 0)
    (harea : area v x ≠ 0)
    (htarget : (target D0 (AF *ᵥ x) (AS *ᵥ ((J : Matrix (Fin 2) (Fin 2) K) *ᵥ x))).det ≠ 0) :
    let eta := area v x
    let delta := (J : Matrix (Fin 2) (Fin 2) K).det
    let a := AF *ᵥ x
    let b := AS *ᵥ ((J : Matrix (Fin 2) (Fin 2) K) *ᵥ x)
    let theta := (target D0 a b).det
    let qF := lamF ⬝ᵥ b
    let qS := lamS ⬝ᵥ a
    HasCoordinate (join D0 AF) (cycle hF v) lamF (-eta * qF / theta) ∧
    HasCoordinate (join D0 AS) (cycle hS ((J : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) lamS
      (delta * eta * qS / theta) := by sorry

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
  cycleS : join D0 AS *ᵥ cycle hS ((J : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = 0
  closedF : lamF ᵥ* join D0 AF = 0
  closedS : lamS ᵥ* join D0 AS = 0
  area_ne : area v x ≠ 0
  target_ne : (target D0 (AF *ᵥ x) (AS *ᵥ ((J : Matrix (Fin 2) (Fin 2) K) *ᵥ x))).det ≠ 0

namespace CommonStrictData

variable (d : CommonStrictData K I)

def delta : K := (d.J : Matrix (Fin 2) (Fin 2) K).det
def eta : K := area d.v d.x
def a : Index I → K := d.AF *ᵥ d.x
def b : Index I → K := d.AS *ᵥ ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.x)
def theta : K := (target d.D0 d.a d.b).det
def qF : K := d.lamF ⬝ᵥ d.b
def qS : K := d.lamS ⬝ᵥ d.a

theorem coordinate_values (uF uS : K)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)) d.lamS uS) :
    uF = -d.eta * d.qF / d.theta ∧
    uS = d.delta * d.eta * d.qS / d.theta := by sorry

end CommonStrictData

end Research.DerivativeSwitch.ScalarRatio
