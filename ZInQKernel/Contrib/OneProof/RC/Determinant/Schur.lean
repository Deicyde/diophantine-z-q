import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Block Schur complements and one-step Gaussian elimination (Lane RC7, manuscript §9)

This file formalizes the exact block identities used twice in §9 of the manuscript
(`diophantine_zq.tex`, the 11/5 version; Version 19 has the same text at these places):

* tex 5437–5454 (`ex:limits-fixed-field-budget`): cancellation of the invertible new local block
  `B` in a differential `d = (P Q; T B)`, with the surviving Schur differential `P - Q B⁻¹ T`, and the
  statement that the surviving entries of both adjacent differentials are literally unchanged;
* tex 5544–5572 (`ex:limits-fixed-field-clearing`): cancellation of an old Smith block `A_i` in a
  differential `(A_i B; C D')` by two determinant-one elementary matrices, the vanishing of the
  adjacent components into and out of the cancelled pair, and the explicit projection
  `(b, v) ↦ v - C A_i⁻¹ b` and inclusion `v ↦ (-A_i⁻¹ B v, v)` of the elimination.

Block columns are `Matrix.fromRows`, block rows are `Matrix.fromCols`.  Everything here is PROVED
over an arbitrary commutative ring, the only hypothesis being invertibility of the cancelled block.
-/

namespace ZInQ.Manuscript.RC.Determinant

open Matrix

variable {R : Type*} [CommRing R]

section NewLocalBlock

variable {l m n k k' : Type*} [Fintype l] [Fintype m] [Fintype n]
  [DecidableEq l] [DecidableEq m] [DecidableEq n]

/-- **Tex 5442–5446 (PROVED).**  In the two degrees containing the new local block, write the
differential as `d = (P Q; T B)` with `B` invertible.  Then
`(1, -Q B⁻¹; 0, 1) · d · (1, 0; -B⁻¹ T, 1) = (P - Q B⁻¹ T, 0; 0, B)`. -/
theorem schur_block_identity (P : Matrix m l R) (Q : Matrix m n R) (T : Matrix n l R)
    (B : Matrix n n R) (hB : IsUnit B.det) :
    fromBlocks (1 : Matrix m m R) (-(Q * B⁻¹)) (0 : Matrix n m R) (1 : Matrix n n R) *
        fromBlocks P Q T B *
        fromBlocks (1 : Matrix l l R) (0 : Matrix l n R) (-(B⁻¹ * T)) (1 : Matrix n n R) =
      fromBlocks (P - Q * B⁻¹ * T) 0 0 B := by
  have h1 : B * B⁻¹ = 1 := mul_nonsing_inv B hB
  have h2 : B⁻¹ * B = 1 := nonsing_inv_mul B hB
  have h1' : B * (B⁻¹ * T) = T := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_assoc, h2, h1', sub_eq_add_neg]

/-- The right elementary factor of `schur_block_identity` has the evident inverse. -/
theorem schur_right_inverse (T : Matrix n l R) (B : Matrix n n R) :
    fromBlocks (1 : Matrix l l R) (0 : Matrix l n R) (B⁻¹ * T) (1 : Matrix n n R) *
      fromBlocks (1 : Matrix l l R) (0 : Matrix l n R) (-(B⁻¹ * T)) (1 : Matrix n n R) = 1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one]; simp

/-- The left elementary factor of `schur_block_identity` has the evident inverse. -/
theorem schur_left_inverse (Q : Matrix m n R) (B : Matrix n n R) :
    fromBlocks (1 : Matrix m m R) (-(Q * B⁻¹)) (0 : Matrix n m R) (1 : Matrix n n R) *
      fromBlocks (1 : Matrix m m R) (Q * B⁻¹) (0 : Matrix n m R) (1 : Matrix n n R) = 1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one]; simp

omit [Fintype m] [DecidableEq m] in
/-- **Tex 5447–5449 (PROVED).**  If the preceding differential has components `(X, Y)ᵀ`, then
`d² = 0` gives `T X + B Y = 0`, and in the new source coordinates its components are
`(X, B⁻¹ T X + Y)ᵀ = (X, 0)ᵀ`. -/
theorem schur_preceding (P : Matrix m l R) (Q : Matrix m n R) (T : Matrix n l R)
    (B : Matrix n n R) (hB : IsUnit B.det) (X : Matrix l k R) (Y : Matrix n k R)
    (hd2 : fromBlocks P Q T B * fromRows X Y = 0) :
    T * X + B * Y = 0 ∧
      fromBlocks (1 : Matrix l l R) (0 : Matrix l n R) (B⁻¹ * T) (1 : Matrix n n R) *
        fromRows X Y = fromRows X 0 := by
  rw [fromBlocks_mul_fromRows, ← fromRows_zero] at hd2
  have hTB : T * X + B * Y = 0 := (fromRows_inj hd2).2
  refine ⟨hTB, ?_⟩
  have h2 : B⁻¹ * B = 1 := nonsing_inv_mul B hB
  rw [fromBlocks_mul_fromRows]
  congr 1
  · simp
  · calc B⁻¹ * T * X + (1 : Matrix n n R) * Y = B⁻¹ * (T * X + B * Y) := by
          rw [Matrix.mul_add, ← Matrix.mul_assoc B⁻¹ B Y, h2, Matrix.mul_assoc, Matrix.one_mul]
      _ = 0 := by rw [hTB, Matrix.mul_zero]

omit [Fintype l] [DecidableEq l] in
/-- **Tex 5450–5452 (PROVED).**  If the following differential has components `(U, V)`, then
`U Q + V B = 0`, and in the new target coordinates they are `(U, U Q B⁻¹ + V) = (U, 0)`. -/
theorem schur_following (P : Matrix m l R) (Q : Matrix m n R) (T : Matrix n l R)
    (B : Matrix n n R) (hB : IsUnit B.det) (U : Matrix k' m R) (V : Matrix k' n R)
    (hd2 : fromCols U V * fromBlocks P Q T B = 0) :
    U * Q + V * B = 0 ∧
      fromCols U V * fromBlocks (1 : Matrix m m R) (Q * B⁻¹) (0 : Matrix n m R) (1 : Matrix n n R)
        = fromCols U 0 := by
  rw [fromCols_mul_fromBlocks, ← fromCols_zero] at hd2
  have hUV : U * Q + V * B = 0 := (fromCols_inj hd2).2
  refine ⟨hUV, ?_⟩
  have h1 : B * B⁻¹ = 1 := mul_nonsing_inv B hB
  rw [fromCols_mul_fromBlocks]
  congr 1
  · simp
  · calc U * (Q * B⁻¹) + V * (1 : Matrix n n R) = (U * Q + V * B) * B⁻¹ := by
          rw [Matrix.add_mul, Matrix.mul_assoc V B B⁻¹, h1, Matrix.mul_assoc]
      _ = 0 := by rw [hUV, Matrix.zero_mul]

end NewLocalBlock

section OldSmithBlock

variable {e r r' k k' : Type*} [Fintype e] [Fintype r] [Fintype r']
  [DecidableEq e] [DecidableEq r] [DecidableEq r']

/-- **Tex 5544–5553 (PROVED).**  Cancelling an old Smith block `A_i` (from `E_i` to `B_{i+1}`) once,
in `S[1/Δ]` (here: any commutative ring in which `det A_i` is a unit):
`(1, 0; -C A_i⁻¹, 1) (A_i B; C D') (1, -A_i⁻¹ B; 0, 1) = (A_i, 0; 0, D' - C A_i⁻¹ B)`. -/
theorem smith_block_cancel (A : Matrix e e R) (B : Matrix e r R) (C : Matrix r' e R)
    (D' : Matrix r' r R) (hA : IsUnit A.det) :
    fromBlocks (1 : Matrix e e R) (0 : Matrix e r' R) (-(C * A⁻¹)) (1 : Matrix r' r' R) *
        fromBlocks A B C D' *
        fromBlocks (1 : Matrix e e R) (-(A⁻¹ * B)) (0 : Matrix r e R) (1 : Matrix r r R) =
      fromBlocks A 0 0 (D' - C * A⁻¹ * B) := by
  have h1 : A * A⁻¹ = 1 := mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := nonsing_inv_mul A hA
  have h1' : A * (A⁻¹ * B) = B := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_assoc, h2, h1', sub_eq_add_neg] <;> abel

/-- **Tex 5554 (PROVED).**  Both elementary matrices of `smith_block_cancel` have determinant one. -/
theorem smith_elementary_det (A : Matrix e e R) (B : Matrix e r R) (C : Matrix r' e R) :
    (fromBlocks (1 : Matrix e e R) (0 : Matrix e r' R) (-(C * A⁻¹)) (1 : Matrix r' r' R)).det = 1 ∧
      (fromBlocks (1 : Matrix e e R) (-(A⁻¹ * B)) (0 : Matrix r e R) (1 : Matrix r r R)).det = 1 := by
  constructor
  · rw [det_fromBlocks_zero₁₂]; simp
  · rw [det_fromBlocks_zero₂₁]; simp

omit [Fintype r'] [DecidableEq r'] in
/-- **Tex 5554–5557 (PROVED), incoming side.**  If the preceding differential has components
`(X, Y)ᵀ` into `E_i ⊕ (rest)`, then `d² = 0` gives `A_i X + B Y = 0`, and after the source change
its component into the cancelled `E_i` is zero while the component `Y` is unchanged. -/
theorem smith_preceding (A : Matrix e e R) (B : Matrix e r R) (C : Matrix r' e R)
    (D' : Matrix r' r R) (hA : IsUnit A.det) (X : Matrix e k R) (Y : Matrix r k R)
    (hd2 : fromBlocks A B C D' * fromRows X Y = 0) :
    A * X + B * Y = 0 ∧
      fromBlocks (1 : Matrix e e R) (A⁻¹ * B) (0 : Matrix r e R) (1 : Matrix r r R) * fromRows X Y
        = fromRows 0 Y := by
  rw [fromBlocks_mul_fromRows, ← fromRows_zero] at hd2
  have hAB : A * X + B * Y = 0 := (fromRows_inj hd2).1
  refine ⟨hAB, ?_⟩
  have h2 : A⁻¹ * A = 1 := nonsing_inv_mul A hA
  rw [fromBlocks_mul_fromRows]
  congr 1
  · calc (1 : Matrix e e R) * X + A⁻¹ * B * Y = A⁻¹ * (A * X + B * Y) := by
          rw [Matrix.mul_add, ← Matrix.mul_assoc A⁻¹ A X, h2, Matrix.mul_assoc]
      _ = 0 := by rw [hAB, Matrix.mul_zero]
  · simp

omit [Fintype r] [DecidableEq r] in
/-- **Tex 5554–5557 (PROVED), outgoing side.**  If the following differential has components
`(U, V)` out of `B_{i+1} ⊕ (rest)`, then `U A_i + V C = 0`, and after the target change its
component out of the cancelled `B_{i+1}` is zero while `V` is unchanged. -/
theorem smith_following (A : Matrix e e R) (B : Matrix e r R) (C : Matrix r' e R)
    (D' : Matrix r' r R) (hA : IsUnit A.det) (U : Matrix k' e R) (V : Matrix k' r' R)
    (hd2 : fromCols U V * fromBlocks A B C D' = 0) :
    U * A + V * C = 0 ∧
      fromCols U V * fromBlocks (1 : Matrix e e R) (0 : Matrix e r' R) (C * A⁻¹) (1 : Matrix r' r' R)
        = fromCols 0 V := by
  rw [fromCols_mul_fromBlocks, ← fromCols_zero] at hd2
  have hUV : U * A + V * C = 0 := (fromCols_inj hd2).1
  refine ⟨hUV, ?_⟩
  have h1 : A * A⁻¹ = 1 := mul_nonsing_inv A hA
  rw [fromCols_mul_fromBlocks]
  congr 1
  · calc U * (1 : Matrix e e R) + V * (C * A⁻¹) = (U * A + V * C) * A⁻¹ := by
          rw [Matrix.add_mul, Matrix.mul_assoc U A A⁻¹, h1, Matrix.mul_assoc]
      _ = 0 := by rw [hUV, Matrix.zero_mul]
  · simp

/-! ### The explicit projection and inclusion of one elimination step (tex 5562–5572) -/

/-- Tex 5564–5565: the projection associated to the incoming cancellation, `(b, v) ↦ v - C A⁻¹ b`,
on the target degree `B_{i+1} ⊕ (rest)` of the cancelled pair. -/
noncomputable def elimProj (A : Matrix e e R) (C : Matrix r' e R) : Matrix r' (e ⊕ r') R :=
  fromCols (-(C * A⁻¹)) 1

/-- Tex 5567–5569: the inclusion associated to the outgoing cancellation, `v ↦ (-A⁻¹ B v, v)`,
on the source degree `E_i ⊕ (rest)` of the cancelled pair. -/
noncomputable def elimIncl (A : Matrix e e R) (B : Matrix e r R) : Matrix (e ⊕ r) r R :=
  fromRows (-(A⁻¹ * B)) 1

/-- **Tex 5562–5572 (PROVED).**  The elimination maps form a deformation retraction onto the
reduced pair with differential `D' - C A⁻¹ B`: the projections (coordinate projection in the
source degree, `elimProj` in the target degree) and inclusions (`elimIncl` in the source degree,
coordinate inclusion in the target degree) are chain maps, their composites on the reduced pair
are the identity, and `ι ∘ p` is homotopic to the identity through `h = (A⁻¹, 0; 0, 0)`. -/
theorem elim_deformation_retract (A : Matrix e e R) (B : Matrix e r R) (C : Matrix r' e R)
    (D' : Matrix r' r R) (hA : IsUnit A.det) :
    (D' - C * A⁻¹ * B) * fromCols (0 : Matrix r e R) (1 : Matrix r r R) =
        elimProj A C * fromBlocks A B C D' ∧
    fromBlocks A B C D' * elimIncl A B =
        fromRows (0 : Matrix e r' R) (1 : Matrix r' r' R) * (D' - C * A⁻¹ * B) ∧
    fromCols (0 : Matrix r e R) (1 : Matrix r r R) * elimIncl A B = 1 ∧
    elimProj A C * fromRows (0 : Matrix e r' R) (1 : Matrix r' r' R) = 1 ∧
    1 - elimIncl A B * fromCols (0 : Matrix r e R) (1 : Matrix r r R) =
      fromBlocks A⁻¹ (0 : Matrix e r' R) (0 : Matrix r e R) (0 : Matrix r r' R) *
        fromBlocks A B C D' ∧
    1 - fromRows (0 : Matrix e r' R) (1 : Matrix r' r' R) * elimProj A C =
      fromBlocks A B C D' *
        fromBlocks A⁻¹ (0 : Matrix e r' R) (0 : Matrix r e R) (0 : Matrix r r' R) := by
  have h1 : A * A⁻¹ = 1 := mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := nonsing_inv_mul A hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [elimProj, mul_fromCols, fromCols_mul_fromBlocks]
    congr 1
    · rw [Matrix.neg_mul, Matrix.mul_assoc C A⁻¹ A, h2]; simp
    · simp only [Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]; abel
  · rw [elimIncl, fromBlocks_mul_fromRows, fromRows_mul]
    congr 1
    · rw [Matrix.mul_neg, ← Matrix.mul_assoc A A⁻¹ B, h1]; simp
    · simp only [Matrix.mul_one, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_assoc]; abel
  · rw [elimIncl, fromCols_mul_fromRows]; simp
  · rw [elimProj, fromCols_mul_fromRows]; simp
  · rw [sub_eq_iff_eq_add, elimIncl, fromRows_mul_fromCols, fromBlocks_multiply, fromBlocks_add,
      ← fromBlocks_one]
    refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;> simp [h2]
  · rw [sub_eq_iff_eq_add, elimProj, fromRows_mul_fromCols, fromBlocks_multiply, fromBlocks_add,
      ← fromBlocks_one]
    refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;> simp [h1]

/-- **Tex 5559 (PROVED).**  Every inverse used is `adj(A_i)/δ_i`: multiplying the elimination
projection by `δ_i = det A_i` clears its only denominator, and likewise for the inclusion. -/
theorem elim_denominators (A : Matrix e e R) (B : Matrix e r R) (C : Matrix r' e R)
    (hA : IsUnit A.det) :
    A.det • elimProj A C = fromCols (-(C * A.adjugate)) (A.det • (1 : Matrix r' r' R)) ∧
      A.det • elimIncl A B = fromRows (-(A.adjugate * B)) (A.det • (1 : Matrix r r R)) := by
  have hinv : A⁻¹ = Ring.inverse A.det • A.adjugate := inv_def A
  have hu : A.det * Ring.inverse A.det = 1 := Ring.mul_inverse_cancel _ hA
  have key : A.det • A⁻¹ = A.adjugate := by
    rw [hinv, smul_smul, hu, one_smul]
  constructor
  · have hC : A.det • (C * A⁻¹) = C * A.adjugate := by rw [← key, Matrix.mul_smul]
    ext i (j | j)
    · have := congrFun (congrFun hC i) j
      simp only [Matrix.smul_apply] at this
      simp [elimProj, ← this]
    · simp [elimProj]
  · have hB : A.det • (A⁻¹ * B) = A.adjugate * B := by rw [← Matrix.smul_mul, key]
    ext (i | i) j
    · have := congrFun (congrFun hB i) j
      simp only [Matrix.smul_apply] at this
      simp [elimIncl, ← this]
    · simp [elimIncl]

end OldSmithBlock

end ZInQ.Manuscript.RC.Determinant
