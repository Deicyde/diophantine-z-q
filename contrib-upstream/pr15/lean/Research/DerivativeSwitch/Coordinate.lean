import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Adjugate tensor coordinates and changes of frame

Received as an uncompiled candidate. Current verification is recorded in
`research/scalar-ratio/VERIFICATION.md`.
Pinned target: Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.

The coordinate is specified by the full matrix identity `z lambda = u adj(D)`.
It is NOT defined to be the scalar formula we wish to prove.
No Selmer complex, arithmetic functional or determinant-functor bridge is
constructed in this module. All matrix identities use the explicit adjugate
convention recorded in the accompanying mathematical specification.
-/

namespace Research.DerivativeSwitch.ScalarRatio

open Matrix
open scoped Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Column times row, without an implicit pairing convention. -/
def tensor (z lam : n → K) : Matrix n n K := fun i j => z i * lam j

/-- Concrete cofactor specification of the class-functional coordinate. -/
def HasCoordinate (D : Matrix n n K) (z lam : n → K) (u : K) : Prop :=
  tensor z lam = u • D.adjugate

lemma tensor_mul (z lam : n → K) (A : Matrix n n K) :
    tensor z lam * A = tensor z (lam ᵥ* A) := by
  ext i j
  simp only [Matrix.mul_apply, tensor, Matrix.vecMul, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma mul_tensor (A : Matrix n n K) (z lam : n → K) :
    A * tensor z lam = tensor (A *ᵥ z) lam := by
  ext i j
  simp only [Matrix.mul_apply, tensor, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma adjugate_unit (B : (Matrix n n K)ˣ) :
    (B : Matrix n n K).adjugate =
      (B : Matrix n n K).det • (↑B⁻¹ : Matrix n n K) := by
  calc
    (B : Matrix n n K).adjugate =
        (↑B⁻¹ : Matrix n n K) *
          ((B : Matrix n n K) * (B : Matrix n n K).adjugate) := by
            simp [← Matrix.mul_assoc]
    _ = _ := by
      rw [Matrix.mul_adjugate]
      simp

lemma det_unit_inv_mul (B : (Matrix n n K)ˣ) :
    (↑B⁻¹ : Matrix n n K).det * (B : Matrix n n K).det = 1 := by
  rw [← Matrix.det_mul]
  simp

/-- A genuine change-of-frame theorem. Its hypotheses are matrix equations,
not equality of the two determinant coordinates to be compared. -/
theorem coordinate_of_frame
    (D N : Matrix n n K) (B T : (Matrix n n K)ˣ)
    (z lam e ell : n → K) (u : K)
    (hD : D * (B : Matrix n n K) = (T : Matrix n n K) * N)
    (hz : z = (B : Matrix n n K) *ᵥ e)
    (hlam : lam ᵥ* (T : Matrix n n K) = ell)
    (hnormal : HasCoordinate N e ell u) :
    HasCoordinate D z lam
      ((B : Matrix n n K).det / (T : Matrix n n K).det * u) := by
  have hT : (T : Matrix n n K).det ≠ 0 :=
    (Matrix.isUnits_det_units T).ne_zero
  have hD' : D = (T : Matrix n n K) * N * (↑B⁻¹ : Matrix n n K) := by
    have h := congrArg (fun A : Matrix n n K => A * (↑B⁻¹ : Matrix n n K)) hD
    simpa [Matrix.mul_assoc] using h
  have htensor : tensor z lam =
      u • ((B : Matrix n n K) * N.adjugate * (↑T⁻¹ : Matrix n n K)) := by
    calc
      tensor z lam = (tensor z lam * (T : Matrix n n K)) *
          (↑T⁻¹ : Matrix n n K) := by simp [Matrix.mul_assoc]
      _ = tensor z ell * (↑T⁻¹ : Matrix n n K) := by rw [tensor_mul, hlam]
      _ = ((B : Matrix n n K) * tensor e ell) *
          (↑T⁻¹ : Matrix n n K) := by rw [hz, ← mul_tensor]
      _ = _ := by
        rw [hnormal]
        simp
  have hadj : D.adjugate =
      ((↑B⁻¹ : Matrix n n K).det * (T : Matrix n n K).det) •
        ((B : Matrix n n K) * N.adjugate * (↑T⁻¹ : Matrix n n K)) := by
    rw [hD', Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
      adjugate_unit, adjugate_unit]
    simp [smul_smul, Matrix.mul_assoc, mul_comm]
  have hscalar :
      ((B : Matrix n n K).det / (T : Matrix n n K).det * u) *
        ((↑B⁻¹ : Matrix n n K).det * (T : Matrix n n K).det) = u := by
    calc
      _ = u * ((↑B⁻¹ : Matrix n n K).det * (B : Matrix n n K).det) *
          ((T : Matrix n n K).det / (T : Matrix n n K).det) := by ring
      _ = u := by rw [det_unit_inv_mul, div_self hT]; ring
  change tensor z lam = _
  rw [htensor, hadj, smul_smul, hscalar]

/-- Rank-one normal differential: identity on every coordinate except `k`. -/
def normal (k : n) : Matrix n n K :=
  Matrix.diagonal (fun i => if i = k then 0 else 1)

/-- The adjugate is the projector onto the unique kernel coordinate. -/
lemma adjugate_normal (k : n) :
    (normal (K := K) k).adjugate = tensor (Pi.single k 1) (Pi.single k 1) := by
  classical
  have hp (i : n) :
      (∏ j ∈ Finset.univ.erase i, (if j = k then (0 : K) else 1)) =
        if i = k then 1 else 0 := by
    by_cases hi : i = k
    · subst i
      rw [ite_eq_left rfl]
      apply Finset.prod_eq_one
      intro j hj
      have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
      simp [hjk]
    · rw [ite_eq_right hi]
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ k⟩)
      simp
  rw [normal, Matrix.adjugate_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, hp, tensor, Pi.single_apply]
  by_cases hi : i = k <;> by_cases hj : j = k <;> by_cases hij : i = j <;>
    simp_all

lemma normal_coordinate (k : n) (q : K) :
    HasCoordinate (normal k) (Pi.single k 1) (q • Pi.single k 1) q := by
  unfold HasCoordinate
  rw [adjugate_normal]
  ext i j
  simp [tensor, mul_left_comm]

/-- Row-vector associativity, spelled out to avoid an implicit transpose convention. -/
lemma row_mul_assoc (lam : n → K) (A B : Matrix n n K) :
    (lam ᵥ* A) ᵥ* B = lam ᵥ* (A * B) := by
  ext j
  simp only [Matrix.vecMul, Matrix.mul_apply, dotProduct]
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

lemma row_normal_apply (r : n → K) (k i : n) :
    (r ᵥ* normal k) i = r i * (if i = k then 0 else 1) := by
  classical
  simp [normal, Matrix.vecMul, dotProduct, Matrix.diagonal_apply, mul_ite]

/-- Closedness, not a guessed normalization, determines the normal row.
The remaining coefficient is literally evaluation on column `k` of `T`. -/
lemma closed_row_in_frame
    (D : Matrix n n K) (B T : (Matrix n n K)ˣ)
    (lam : n → K) (k : n)
    (hD : D * (B : Matrix n n K) = (T : Matrix n n K) * normal k)
    (hclosed : lam ᵥ* D = 0) :
    lam ᵥ* (T : Matrix n n K) =
      ((lam ᵥ* (T : Matrix n n K)) k) • Pi.single k 1 := by
  have hz : (lam ᵥ* (T : Matrix n n K)) ᵥ* normal k = 0 := by
    rw [row_mul_assoc, ← hD, ← row_mul_assoc, hclosed]
    simp
  ext i
  by_cases hi : i = k
  · subst i
    simp
  · have hzi := congrFun hz i
    rw [row_normal_apply] at hzi
    have hvalue : (lam ᵥ* (T : Matrix n n K)) i = 0 := by
      simpa [hi] using hzi
    simp [hi, hvalue]

/-- General-size coordinate formula from a rank-one frame and the actual
closed functional. No cross-boundary normalization is assumed. -/
theorem coordinate_of_closed_frame
    (D : Matrix n n K) (B T : (Matrix n n K)ˣ)
    (z lam : n → K) (k : n)
    (hD : D * (B : Matrix n n K) = (T : Matrix n n K) * normal k)
    (hz : z = (B : Matrix n n K) *ᵥ Pi.single k 1)
    (hclosed : lam ᵥ* D = 0) :
    HasCoordinate D z lam
      ((B : Matrix n n K).det / (T : Matrix n n K).det *
        (lam ᵥ* (T : Matrix n n K)) k) := by
  exact coordinate_of_frame D (normal k) B T z lam
    (Pi.single k 1)
    (((lam ᵥ* (T : Matrix n n K)) k) • Pi.single k 1)
    ((lam ᵥ* (T : Matrix n n K)) k)
    hD hz (closed_row_in_frame D B T lam k hD hclosed) (normal_coordinate k _)

/-- The frame conditions force a nonzero adjugate; rank n-1 is not
silently assumed in the coordinate uniqueness application. -/
lemma adjugate_ne_zero_of_frame
    (D : Matrix n n K) (B T : (Matrix n n K)ˣ) (k : n)
    (hD : D * (B : Matrix n n K) = (T : Matrix n n K) * normal k) :
    D.adjugate ≠ 0 := by
  have h := congrArg Matrix.adjugate hD
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib] at h
  intro hz
  rw [hz, Matrix.mul_zero] at h
  have h' := congrArg (fun A : Matrix n n K => A * (T : Matrix n n K)) h
  have hzero : (T : Matrix n n K).det • (normal (K := K) k).adjugate = 0 := by
    simpa [Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.mul_smul] using h'.symm
  have hkk := congrFun (congrFun hzero k) k
  apply (Matrix.isUnits_det_units T).ne_zero
  simpa [adjugate_normal, tensor, Pi.single_apply] using hkk

/-- Coordinates are unique whenever the adjugate is nonzero. -/
theorem coordinate_unique
    (D : Matrix n n K) (z lam : n → K) (u w : K)
    (hadj : D.adjugate ≠ 0)
    (hu : HasCoordinate D z lam u) (hw : HasCoordinate D z lam w) : u = w := by
  classical
  have hex : ∃ i j, D.adjugate i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hadj
    ext i j
    exact h i j
  obtain ⟨i, j, hij⟩ := hex
  have heq := congrFun (congrFun (hu.symm.trans hw) i) j
  apply mul_right_cancel₀ hij
  simpa using heq

end Research.DerivativeSwitch.ScalarRatio
