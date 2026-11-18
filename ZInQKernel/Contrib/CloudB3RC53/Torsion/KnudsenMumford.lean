import ZInQKernel.Contrib.CloudB3RC53.Torsion.Operations
import ZInQKernel.Contrib.CloudB3RC53.Torsion.Bordered
import ZInQKernel.Contrib.OneProof.RC.Central.Coordinate

/-!
# Torsion, part 4: the Knudsen–Mumford coordinate of `[z] ⊗ [λ]`

For a complex `C⁰ → C¹ → C² → C³` of finite free modules with bases (`FourCx`), a cycle
`z ∈ C¹` (`d¹ z = 0`) and a closed functional `λ` on `C²` (`λ d¹ = 0`), the **augmented complex**

  `C⁰ ⊕ R --(d⁰, z)--> C¹ --d¹--> C² --(d², λ)--> C³ ⊕ R`

(`FourCx.aug`) is exact exactly when `[z]` generates `H¹`, `λ` induces an isomorphism on `H²`
and `H⁰ = H³ = 0` (for a complex with `H¹ ≅ H²` of rank one). Its torsion is the coordinate of
`[z] ⊗ [λ]` in the determinant line `det⁻¹ C ≅ H¹ ⊗ (H²)^*` (Knudsen–Mumford): `kmCoord`
(tex L3877–3892, the coordinate of Definition `ex:arith-coordinate`).

* `FourCx.toBased`: the based complex of a four-term complex (degrees `0, 1, 2, 3`).
* `FourCx.aug`, `kmCoord`.
* `twoTerm D`: RC15's two-term complex `[R^n --D--> R^n]` in degrees one and two.
* `tau_aug_twoTerm`, `kmCoord_twoTerm` (**consistency with RC15**): over a domain, if the augmented
  complex of `twoTerm D` is acyclic and `IsClassFunctionalCoord D z λ u`
  (`z ⊗ λ = u · adj D`), then `kmCoord = u` in the orientation `σ₀ = Equiv.sumComm`.
* `twoTermContraction_example`: the hypotheses are inhabited (`D = (0)`, `z = λ = u = 1`).

**Sign convention.** `kmCoord := −τ(aug)`: with the orientation `σ₀` the torsion of the augmented
two-term complex is `−u` (the bordered determinant `det [[D, c], [rᵀ, 0]] = −r · adj(D) c`); the
sign normalizes the coordinate to RC15's.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Torsion

open Matrix

variable {R : Type*} [CommRing R]

/-- A complex `C⁰ → C¹ → C² → C³` of finite free modules with bases `ι0, …, ι3`. -/
structure FourCx (R : Type*) [CommRing R] (ι0 ι1 ι2 ι3 : Type*) [Fintype ι1] [Fintype ι2] where
  d0 : Matrix ι1 ι0 R
  d1 : Matrix ι2 ι1 R
  d2 : Matrix ι3 ι2 R
  d10 : d1 * d0 = 0
  d21 : d2 * d1 = 0

variable {ι0 ι1 ι2 ι3 : Type*} [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]

/-- The based complex of a four-term complex: even part `C⁰ ⊕ C²`, odd part `C¹ ⊕ C³`. -/
def FourCx.toBased (C : FourCx R ι0 ι1 ι2 ι3) : BasedCx R (ι0 ⊕ ι2) (ι1 ⊕ ι3) where
  degE := Sum.elim (fun _ => 0) (fun _ => 2)
  degO := Sum.elim (fun _ => 1) (fun _ => 3)
  even_degE := by rintro (i | i); exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
  odd_degO := by rintro (i | i); exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
  dOE := fromBlocks C.d0 0 0 C.d2
  dEO := fromBlocks 0 0 C.d1 0
  dd_E := by rw [fromBlocks_multiply]; simp [C.d10]
  dd_O := by rw [fromBlocks_multiply]; simp [C.d21]
  deg_dOE := by
    rintro (i | i) (j | j) h
    · rfl
    · exact absurd rfl h
    · exact absurd rfl h
    · rfl
  deg_dEO := by
    rintro (i | i) (j | j) h
    · exact absurd rfl h
    · exact absurd rfl h
    · rfl
    · exact absurd rfl h

theorem FourCx.toBased_degE (C : FourCx R ι0 ι1 ι2 ι3) :
    C.toBased.degE = Sum.elim (fun _ => 0) (fun _ => 2) := rfl

theorem FourCx.toBased_degO (C : FourCx R ι0 ι1 ι2 ι3) :
    C.toBased.degO = Sum.elim (fun _ => 1) (fun _ => 3) := rfl

theorem FourCx.toBased_dOE (C : FourCx R ι0 ι1 ι2 ι3) :
    C.toBased.dOE = fromBlocks C.d0 0 0 C.d2 := rfl

theorem FourCx.toBased_dEO (C : FourCx R ι0 ι1 ι2 ι3) :
    C.toBased.dEO = fromBlocks 0 0 C.d1 0 := rfl

variable [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]

/-- **The augmented complex** `C⁰ ⊕ R --(d⁰, z)--> C¹ --d¹--> C² --(d², λ)--> C³ ⊕ R`. -/
def FourCx.aug (C : FourCx R ι0 ι1 ι2 ι3) (z : ι1 → R) (lam : ι2 → R) (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) : FourCx R (ι0 ⊕ Unit) ι1 ι2 (ι3 ⊕ Unit) where
  d0 := fromCols C.d0 (replicateCol Unit z)
  d1 := C.d1
  d2 := fromRows C.d2 (replicateRow Unit lam)
  d10 := by
    ext i (j | j)
    · simpa [mul_apply, fromCols_apply_inl] using congrFun (congrFun C.d10 i) j
    · simpa [mul_apply, fromCols_apply_inr, mulVec, dotProduct] using congrFun hz i
  d21 := by
    ext (i | i) j
    · simpa [mul_apply, fromRows_apply_inl] using congrFun (congrFun C.d21 i) j
    · simpa [mul_apply, fromRows_apply_inr, vecMul, dotProduct] using congrFun hlam j

/-- **The Knudsen–Mumford coordinate** of `[z] ⊗ [λ]`: minus the torsion of the augmented complex,
oriented by `σ`. -/
noncomputable def kmCoord (C : FourCx R ι0 ι1 ι2 ι3) (z : ι1 → R) (lam : ι2 → R)
    (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) : R :=
  -torsion (C.aug z lam hz hlam).toBased σ

/-! ### The two-term case: consistency with RC15 -/

variable {n : ℕ}

/-- RC15's two-term complex `[R^n --D--> R^n]` in degrees one and two. -/
def twoTerm (D : Matrix (Fin n) (Fin n) R) : FourCx R Empty (Fin n) (Fin n) Empty where
  d0 := 0
  d1 := D
  d2 := 0
  d10 := by simp
  d21 := by simp

/-- The standard orientation of the augmented two-term complex. -/
def σ₀ (n : ℕ) : (Empty ⊕ Unit) ⊕ Fin n ≃ Fin n ⊕ (Empty ⊕ Unit) := Equiv.sumComm _ _

/-- **The torsion of the augmented two-term complex is `−u`** (over a domain), for any
contraction. -/
theorem tau_aug_twoTerm [IsDomain R] (D : Matrix (Fin n) (Fin n) R) (z w : Fin n → R) (u : R)
    (hz : (twoTerm D).d1 *ᵥ z = 0) (hw : w ᵥ* (twoTerm D).d1 = 0)
    (h : Contraction ((twoTerm D).aug z w hz hw).toBased)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D z w u) :
    tau ((twoTerm D).aug z w hz hw).toBased h (σ₀ n) = -u := by
  set c : Fin n → R := fun i => h.hEO (Sum.inr i) (Sum.inr (Sum.inr ()))
  set r : Fin n → R := fun j => h.hEO (Sum.inl (Sum.inr ())) (Sum.inl j)
  -- degree vanishing of the contraction
  have hdeg : ∀ x y, ((twoTerm D).aug z w hz hw).toBased.degE x ≠
      ((twoTerm D).aug z w hz hw).toBased.degO y - 1 → h.hEO x y = 0 := by
    intro x y hxy
    by_contra hne
    exact hxy (by have := h.deg_hEO x y hne; omega)
  -- (F1) `r · z = 1` (degree zero of `dh + hd = 1`)
  have F1 : r ⬝ᵥ z = 1 := by
    have e := congrFun (congrFun h.htpy_E (Sum.inl (Sum.inr ()))) (Sum.inl (Sum.inr ()))
    simp only [FourCx.toBased_dEO, FourCx.toBased_dOE, Matrix.add_apply, mul_apply,
      Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
      zero_add, one_apply_eq] at e
    simpa [FourCx.aug, fromCols_apply_inr, dotProduct, r] using e
  -- (F2) `λ · c = 1` (degree three of `dh + hd = 1`)
  have F2 : w ⬝ᵥ c = 1 := by
    have e := congrFun (congrFun h.htpy_O (Sum.inr (Sum.inr ()))) (Sum.inr (Sum.inr ()))
    simp only [FourCx.toBased_dEO, FourCx.toBased_dOE, Matrix.add_apply, mul_apply,
      Fintype.sum_sum_type, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
      zero_add, one_apply_eq] at e
    simpa [FourCx.aug, fromRows_apply_inr, dotProduct, c] using e
  -- (F3) the odd torsion is the bordered determinant
  have F3 : tauOdd _ h (σ₀ n) =
      (fromBlocks D (replicateCol Unit c) (replicateRow Unit r) 0).det := by
    unfold tauOdd
    let e : Fin n ⊕ Unit ≃ (Empty ⊕ Unit) ⊕ Fin n :=
      (Equiv.sumCongr (Equiv.refl _) (Equiv.emptySum Empty Unit).symm).trans (Equiv.sumComm _ _)
    rw [← det_submatrix_equiv_self e]
    congr 1
    ext (i | i) (j | j)
    · have h0 : h.hEO (Sum.inr i) (Sum.inl j) = 0 := hdeg _ _ (by simp [FourCx.toBased_degE,
        FourCx.toBased_degO])
      simp [e, σ₀, FourCx.toBased_dEO, FourCx.aug, twoTerm, h0]
    · simp [e, σ₀, FourCx.toBased_dEO, c]
    · simp [e, σ₀, FourCx.toBased_dEO, r]
    · have h0 : h.hEO (Sum.inl (Sum.inr ())) (Sum.inr (Sum.inr ())) = 0 :=
        hdeg _ _ (by simp [FourCx.toBased_degE, FourCx.toBased_degO])
      simp [e, σ₀, FourCx.toBased_dEO, h0]
  -- `u · (r · adj(D) c) = 1`
  have F4 : u * (r ⬝ᵥ (D.adjugate *ᵥ c)) = 1 := by
    have hu' : ∀ i j, u * D.adjugate i j = z i * w j := fun i j => by
      have := congrFun (congrFun hu i) j
      simpa [vecMulVec_apply] using this.symm
    calc u * (r ⬝ᵥ (D.adjugate *ᵥ c))
        = ∑ i, ∑ j, r i * (u * D.adjugate i j) * c j := by
          simp only [dotProduct, mulVec, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = (r ⬝ᵥ z) * (w ⬝ᵥ c) := by
          simp only [hu', dotProduct, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = 1 := by rw [F1, F2, one_mul]
  have key := tau_mul_tauOdd _ h h (σ₀ n)
  rw [F3, det_bordered] at key
  calc tau _ h (σ₀ n) = tau _ h (σ₀ n) * (u * (r ⬝ᵥ (D.adjugate *ᵥ c))) := by rw [F4, mul_one]
    _ = -u * (tau _ h (σ₀ n) * -(r ⬝ᵥ (D.adjugate *ᵥ c))) := by ring
    _ = -u := by rw [key, mul_one]

/-- **Consistency with RC15**: the Knudsen–Mumford coordinate of the augmented two-term complex is
RC15's class-functional coordinate. -/
theorem kmCoord_twoTerm [IsDomain R] (D : Matrix (Fin n) (Fin n) R) (z w : Fin n → R) (u : R)
    (hz : (twoTerm D).d1 *ᵥ z = 0) (hw : w ᵥ* (twoTerm D).d1 = 0)
    (h : Contraction ((twoTerm D).aug z w hz hw).toBased)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D z w u) :
    kmCoord (twoTerm D) z w hz hw (σ₀ n) = u := by
  unfold kmCoord
  rw [← tau_eq_torsion _ h, tau_aug_twoTerm D z w u hz hw h hu, neg_neg]

/-! ### Non-vacuity -/

theorem twoTerm_zero_hz : (twoTerm (0 : Matrix (Fin 1) (Fin 1) R)).d1 *ᵥ (1 : Fin 1 → R) = 0 := by
  simp [twoTerm]

theorem twoTerm_zero_hw : (1 : Fin 1 → R) ᵥ* (twoTerm (0 : Matrix (Fin 1) (Fin 1) R)).d1 = 0 := by
  simp [twoTerm]

/-- A contraction of the augmented complex `R --1--> R --0--> R --1--> R` (`D = (0)`,
`z = λ = 1`). -/
def twoTermContraction_example :
    Contraction ((twoTerm (0 : Matrix (Fin 1) (Fin 1) R)).aug 1 1 twoTerm_zero_hz
      twoTerm_zero_hw).toBased where
  hOE := 0
  hEO := fromBlocks (of fun _ _ => 1) 0 0 (of fun _ _ => 1)
  deg_hOE _ _ h := absurd rfl h
  deg_hEO := by
    rintro ((e | u) | i) (j | (e' | u')) h
    all_goals first | exact e.elim | exact e'.elim | rfl | exact absurd rfl h
  htpy_E := by
    ext ((e | u) | i) ((e' | u') | i')
    all_goals try first | exact e.elim | exact e'.elim
    all_goals ((try fin_cases i); (try fin_cases i'))
    all_goals simp [FourCx.toBased_dEO, FourCx.toBased_dOE, FourCx.aug, twoTerm, mul_apply,
      Fintype.sum_sum_type]
  htpy_O := by
    ext (i | (e | u)) (i' | (e' | u'))
    all_goals try first | exact e.elim | exact e'.elim
    all_goals ((try fin_cases i); (try fin_cases i'))
    all_goals simp [FourCx.toBased_dEO, FourCx.toBased_dOE, FourCx.aug, twoTerm, mul_apply,
      Fintype.sum_sum_type]

/-- **Non-vacuity of `kmCoord_twoTerm`**: `D = (0)`, `z = λ = 1`, `u = 1`. -/
theorem kmCoord_twoTerm_example [IsDomain R] :
    kmCoord (twoTerm (0 : Matrix (Fin 1) (Fin 1) R)) 1 1 twoTerm_zero_hz twoTerm_zero_hw (σ₀ 1)
      = 1 :=
  kmCoord_twoTerm _ _ _ 1 _ _ twoTermContraction_example (by
    unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    ext i j
    fin_cases i; fin_cases j
    simp [vecMulVec_apply, adjugate_fin_one])

end ZInQ.Contrib.CloudB3RC53.Torsion
