module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Degree zero and arbitrary scalar extension -/

@[expose] public section

namespace RC.ModelInvariants

open DirectSum
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (grading : ℤ → Submodule R S) [GradedAlgebra grading]

/-- The component of degree zero, viewed as an algebra over the base ring. -/
abbrev degreeZero : Subalgebra R S := SetLike.GradeZero.subalgebra grading

/-- The projection to degree zero is linear over the degree-zero subalgebra. -/
def degreeZeroProjection : S →ₗ[degreeZero grading] degreeZero grading where
  toFun x := decompose grading x 0
  map_add' x y := by
    apply Subtype.ext
    change ((decompose grading (x + y) 0 : grading 0) : S) =
      (decompose grading x 0 : S) + (decompose grading y 0 : S)
    rw [DirectSum.decompose_add]
    rfl
  map_smul' a x := by
    apply Subtype.ext
    exact coe_decompose_mul_of_left_mem_zero grading a.property

theorem degreeZeroProjection_fixed (x : degreeZero grading) :
    degreeZeroProjection grading (x : S) = x :=
  Subtype.ext (decompose_of_mem_same grading x.property)

variable (R' : Type*) [CommRing R'] [Algebra R R']

/-- Scalar extension of a graded algebra commutes with taking its degree-zero part.
Mathlib's base-change grading tensors each homogeneous summand. -/
noncomputable def degreeZeroBaseChange :
    (R' ⊗[R] degreeZero grading) ≃ₐ[R']
      degreeZero (fun n => (grading n).baseChange R') := by
  let f := Algebra.TensorProduct.map (AlgHom.id R' R') (degreeZero grading).val
  have hf : ∀ x, f x ∈ degreeZero (fun n => (grading n).baseChange R') :=
    fun x => ⟨x, rfl⟩
  exact AlgEquiv.ofBijective (f.codRestrict _ hf) (toBaseChange_bijective grading 0)

theorem degreeZeroBaseChange_tmul (a : R') (x : degreeZero grading) :
    (degreeZeroBaseChange grading R' (a ⊗ₜ[R] x) : R' ⊗[R] S) = a ⊗ₜ[R] (x : S) := rfl

#print axioms degreeZeroProjection
#print axioms degreeZeroProjection_fixed
#print axioms degreeZeroBaseChange
#print axioms degreeZeroBaseChange_tmul

end RC.ModelInvariants
