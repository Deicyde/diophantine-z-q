import Mathlib

/-!
# Torsion, part 3: the matrix determinant lemma and bordered determinants

* `det_add_vecMulVec` (the matrix determinant lemma, without invertibility):
  `det (A + c rᵀ) = det A + r · adj(A) c`.
* `det_bordered`: `det [[A, c], [rᵀ, 0]] = −(r · adj(A) c)`.

These link the adjugate (RC15's class-functional coordinate) to determinants (torsion).

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Torsion

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- `A` with the columns in `s` perturbed by `c rᵀ`. -/
private def pert (A : Matrix n n R) (c r : n → R) (s : Finset n) : Matrix n n R :=
  A + of fun a b => if b ∈ s then c a * r b else 0

private theorem det_updateCol_pert (A : Matrix n n R) (c r : n → R) (s : Finset n) (k : n)
    (hk : k ∉ s) : ((pert A c r s).updateCol k c).det = (A.updateCol k c).det := by
  set r' : n → R := fun b => if b ∈ s then r b else 0
  have key : (pert A c r s).updateCol k c =
      A.updateCol k c * (1 + replicateCol Unit (Pi.single k (1 : R)) * replicateRow Unit r') := by
    ext a b
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, ← Matrix.mul_assoc]
    simp only [mul_apply, replicateCol_apply, replicateRow_apply, Fintype.univ_unit,
      Finset.sum_singleton, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, updateCol_self, pert, r']
    by_cases hb : b = k
    · subst hb; simp [hk]
    · simp only [updateCol_apply, hb, ↓reduceIte, Matrix.add_apply, of_apply]
  rw [key, det_mul, det_one_add_replicateCol_mul_replicateRow]
  simp [r', dotProduct, Pi.single_apply, hk]

private theorem det_pert (A : Matrix n n R) (c r : n → R) (s : Finset n) :
    (pert A c r s).det = A.det + ∑ i ∈ s, r i * (A.updateCol i c).det := by
  induction s using Finset.induction_on with
  | empty => rw [show pert A c r ∅ = A by ext; simp [pert]]; simp
  | insert k s hk ih =>
    have hcol : pert A c r (insert k s) =
        (pert A c r s).updateCol k ((fun a => pert A c r s a k) + r k • c) := by
      ext a b
      by_cases hb : b = k
      · subst hb; simp [pert, hk, mul_comm]
      · simp [pert, hb]
    rw [hcol, Finset.sum_insert hk, det_updateCol_add, det_updateCol_smul,
      det_updateCol_pert _ _ _ _ _ hk]
    have : (pert A c r s).updateCol k (fun a => pert A c r s a k) = pert A c r s := by
      ext a b
      by_cases hb : b = k
      · subst hb; simp
      · simp [hb]
    rw [this, ih]; ring

/-- **The matrix determinant lemma** (no invertibility): `det (A + c rᵀ) = det A + r · adj(A) c`. -/
theorem det_add_vecMulVec (A : Matrix n n R) (c r : n → R) :
    (A + vecMulVec c r).det = A.det + r ⬝ᵥ (A.adjugate *ᵥ c) := by
  have : A + vecMulVec c r = pert A c r Finset.univ := by
    ext a b; simp [pert, vecMulVec_apply]
  rw [this, det_pert, ← cramer_eq_adjugate_mulVec]
  simp [dotProduct, cramer_apply]

/-- **Bordered determinant**: `det [[A, c], [rᵀ, 0]] = −(r · adj(A) c)`. -/
theorem det_bordered (A : Matrix n n R) (c r : n → R) :
    (fromBlocks A (replicateCol Unit c) (replicateRow Unit r) 0).det =
      -(r ⬝ᵥ (A.adjugate *ᵥ c)) := by
  set B0 := fromBlocks A (replicateCol Unit c) (replicateRow Unit r) (0 : Matrix Unit Unit R)
  have h1 : (fromBlocks A (replicateCol Unit c) (replicateRow Unit r) (1 : Matrix Unit Unit R)).det
      = (A + vecMulVec c (-r)).det := by
    rw [det_fromBlocks_one₂₂]
    congr 1
    ext a b; simp [vecMulVec_apply, mul_apply, sub_eq_add_neg]
  have hsplit : fromBlocks A (replicateCol Unit c) (replicateRow Unit r) (1 : Matrix Unit Unit R) =
      B0.updateCol (Sum.inr ())
        (fun x => B0 x (Sum.inr ()) + (Pi.single (Sum.inr ()) (1 : R) : n ⊕ Unit → R) x) := by
    ext (a | a) (b | b) <;> simp [B0, Pi.single_apply]
  have hself : B0.updateCol (Sum.inr ()) (fun x => B0 x (Sum.inr ())) = B0 := by
    ext a (b | b) <;> simp
  have hlast : B0.updateCol (Sum.inr ()) (Pi.single (Sum.inr ()) (1 : R) : n ⊕ Unit → R) =
      fromBlocks A 0 (replicateRow Unit r) (1 : Matrix Unit Unit R) := by
    ext (a | a) (b | b) <;> simp [B0]
  have h2 := det_updateCol_add B0 (Sum.inr ()) (fun x => B0 x (Sum.inr ()))
    (Pi.single (Sum.inr ()) (1 : R) : n ⊕ Unit → R)
  rw [show (fun x => B0 x (Sum.inr ())) + (Pi.single (Sum.inr ()) (1 : R) : n ⊕ Unit → R) =
      fun x => B0 x (Sum.inr ()) + (Pi.single (Sum.inr ()) (1 : R) : n ⊕ Unit → R) x from rfl,
    ← hsplit, h1, hself,
    hlast, det_fromBlocks_zero₁₂, det_one, mul_one, det_add_vecMulVec] at h2
  have : (-r) ⬝ᵥ (A.adjugate *ᵥ c) = -(r ⬝ᵥ (A.adjugate *ᵥ c)) := neg_dotProduct _ _
  rw [this] at h2
  linear_combination -h2

end ZInQ.Contrib.CloudB3RC53.Torsion
