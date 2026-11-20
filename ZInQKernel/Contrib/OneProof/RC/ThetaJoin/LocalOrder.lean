import ZInQKernel.Contrib.OneProof.RC.Adelic.Level
import ZInQKernel.Contrib.OneProof.RC.DivisionJoin.Identification

/-! The split and division coordinates of the level order used in Appendix F. -/

noncomputable section

open scoped Quaternion

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler LocalWeights Matrix

private theorem matrix_mul_complement {K : Type*} [Field K] (A : Mat K) :
    A * (algebraMap K (Mat K) A.trace - A) = algebraMap K (Mat K) A.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.algebraMap_matrix_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

/-- The matrix reduced invariants agree with quaternion trace and norm. -/
theorem split_invariants {K : Type*} [Field K] (a b : K)
    (E : ℍ[K,a,0,b] ≃ₐ[K] Mat K) (x : ℍ[K,a,0,b]) :
    (E x).trace = 2 * x.re ∧ (E x).det = (x * star x).re := by
  have hmat : x * (algebraMap K ℍ[K,a,0,b] (E x).trace - x) =
      algebraMap K ℍ[K,a,0,b] (E x).det := by
    apply E.injective
    simpa only [map_sub, map_mul, AlgEquiv.commutes] using matrix_mul_complement (E x)
  have hstar : algebraMap K ℍ[K,a,0,b] (2 * x.re) - x = star x := by
    apply sub_eq_of_eq_add
    rw [QuaternionAlgebra.coe_algebraMap]
    simpa only [zero_mul, add_zero, zero_add, add_comm] using (QuaternionAlgebra.self_add_star' x).symm
  have hnrd : x * (algebraMap K ℍ[K,a,0,b] (2 * x.re) - x) =
      algebraMap K ℍ[K,a,0,b] (x * star x).re := by
    rw [hstar, QuaternionAlgebra.coe_algebraMap]
    exact QuaternionAlgebra.mul_star_eq_coe x
  have hd : x * algebraMap K ℍ[K,a,0,b] ((E x).trace - 2 * x.re) =
      algebraMap K ℍ[K,a,0,b] ((E x).det - (x * star x).re) := by
    rw [map_sub, mul_sub, map_sub]
    rw [mul_sub] at hmat hnrd
    linear_combination (norm := abel) hmat - hnrd
  have ht : (E x).trace = 2 * x.re := by
    by_contra hne
    have hz : (E x).trace - 2 * x.re ≠ 0 := sub_ne_zero.mpr hne
    rw [QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.mul_coe_eq_smul] at hd
    have hi : x.imI = 0 := by
      have hh := congrArg QuaternionAlgebra.imI hd
      exact (mul_eq_zero.mp hh).resolve_left hz
    have hj : x.imJ = 0 := by
      have hh := congrArg QuaternionAlgebra.imJ hd
      exact (mul_eq_zero.mp hh).resolve_left hz
    have hk : x.imK = 0 := by
      have hh := congrArg QuaternionAlgebra.imK hd
      exact (mul_eq_zero.mp hh).resolve_left hz
    have hx : x = algebraMap K ℍ[K,a,0,b] x.re := QuaternionAlgebra.ext rfl hi hj hk
    have he : E x = algebraMap K (Mat K) x.re := by rw [hx, E.commutes]; rfl
    apply hne
    rw [he]
    simp [Matrix.trace_fin_two, Matrix.algebraMap_matrix_apply, two_mul]
  exact ⟨ht, QuaternionAlgebra.algebraMap_injective (by rw [ht, hnrd] at hmat; exact hmat.symm)⟩

variable (ell : ℕ) [Fact ell.Prime] (h : ell % 4 = 3)
variable (N : ℕ) (hN : 0 < N)

private def linearSplit (p : Prime) (hp : p.val ≠ ell) :
    Bp p.val (-1) (-(ell : ℚ)) ≃ₐ[ℤ_[p.val]] Mat ℚ_[p.val] where
  __ := (splitChart ell h p hp).toRingEquiv
  commutes' r := (splitChart ell h p hp).commutes (r : ℚ_[p.val])

private theorem integralMatrix_injective (p : Prime) :
    Function.Injective (matrixCastAlg p) := by
  intro A B hAB
  apply Matrix.ext
  intro i j
  exact Subtype.val_injective (congrFun (congrFun hAB i) j)

private theorem split_image (p : Prime) (hp : p.val ≠ ell) :
    ((levelOrder ell h N hN).completion p.val).map (linearSplit ell h p hp).toAlgHom =
      standardOrder p (N.factorization p.val) := by
  ext A
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [levelOrder_completion] at hx
    exact (levelLocal_mem_split ell h N p hp x).mp hx
  · intro hA
    let E := linearSplit ell h p hp
    refine ⟨E.symm A, ?_, E.apply_symm_apply A⟩
    rw [levelOrder_completion]
    exact (levelLocal_mem_split ell h N p hp _).mpr
      (show E (E.symm A) ∈ _ by rwa [E.apply_symm_apply])

/-- The completed order in the chosen split chart. -/
def splitOrderEquiv (p : Prime) (hp : p.val ≠ ell) :
    (levelOrder ell h N hN).completion p.val ≃ₐ[ℤ_[p.val]]
      eichler p.val (N.factorization p.val) :=
  ((linearSplit ell h p hp).subalgebraMap _).trans
    ((Subalgebra.equivOfEq _ _ (split_image ell h N hN p hp)).trans
      ((eichler p.val (N.factorization p.val)).equivMapOfInjective (matrixCastAlg p)
        (integralMatrix_injective p)).symm)

theorem splitOrderEquiv_apply (p : Prime) (hp : p.val ≠ ell)
    (x : (levelOrder ell h N hN).completion p.val) :
    integralMat p.val (splitOrderEquiv ell h N hN p hp x).val =
      splitChart ell h p hp x.val := by
  change (matrixCastAlg p) _ = _
  exact congrArg Subtype.val
    (((eichler p.val (N.factorization p.val)).equivMapOfInjective (matrixCastAlg p)
        (integralMatrix_injective p)).apply_symm_apply
      ((Subalgebra.equivOfEq _ _ (split_image ell h N hN p hp))
        ((linearSplit ell h p hp).subalgebraMap _ x)))

/-- The action on the cyclic quotient, expressed in the chosen bottom coordinate. -/
def cyclicAction (p : Prime) (hp : p.val ≠ ell) :
    (levelOrder ell h N hN).completion p.val →+* ZMod (p.val ^ N.factorization p.val) :=
  (level p.val _).comp (splitOrderEquiv ell h N hN p hp).toRingHom

/-- The actual split identification used by the level-prime weights. -/
def splitIdentification (p : Prime) (hp : p.val ≠ ell) :
    SplitIdentification p.val (N.factorization p.val)
      ((levelOrder ell h N hN).completion p.val) (Bp p.val (-1) (-(ell : ℚ)))
      ((levelOrder ell h N hN).completion p.val).val.toRingHom
      (fun x => 2 * x.re) (fun x => (x * star x).re) (cyclicAction ell h N hN p hp) where
  order := splitOrderEquiv ell h N hN p hp
  ambient := splitChart ell h p hp
  compatible x := (splitOrderEquiv_apply ell h N hN p hp x).symm
  trace x := (split_invariants _ _ (splitChart ell h p hp) x).1
  norm x := (split_invariants _ _ (splitChart ell h p hp) x).2
  quotient _ := rfl

/-- The level order keeps the explicit maximal order at the discriminant prime. -/
theorem divisionCompletion :
    (levelOrder ell h N hN).completion ell = DivisionJoin.completedOrder ell h := by
  let p : Prime := ⟨ell, Fact.out⟩
  rw [show (levelOrder ell h N hN).completion ell = levelLocal ell h N p from
    levelOrder_completion ell h N hN p, levelLocal, dite_eq_right (not_not.mpr rfl)]

/-- The division identification on the actual level completion. -/
def divisionIdentification :
    letI : Fact (ell % 4 = 3) := ⟨h⟩
    DivisionIdentification (LocalDivision.coordinates ell)
      ((levelOrder ell h N hN).completion ell) (DivisionJoin.LocalB ell)
      ((levelOrder ell h N hN).completion ell).val.toRingHom
      (DivisionJoin.reducedTrace ell) (DivisionJoin.reducedNorm ell) := by
  letI : Fact (ell % 4 = 3) := ⟨h⟩
  rw [divisionCompletion ell h N hN]
  exact DivisionJoin.identification ell

end ZInQ.Manuscript.RC.ThetaJoin
