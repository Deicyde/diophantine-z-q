/-
Plan step 3.2 (effective Dirichlet): the quadratic field `ℚ(√d)` as `QuadraticAlgebra ℚ d 0`.
-/
import Mathlib

namespace ZInQ.Progressions

open NumberField

/-- The quadratic field `ℚ(√d)`, as Mathlib's `QuadraticAlgebra ℚ d 0` (`ω ^ 2 = d`). It is a
field when `d` is not a rational square, e.g. when `d` is squarefree and `d ≠ 1`. -/
abbrev Qsqrt (d : ℤ) : Type := QuadraticAlgebra ℚ (d : ℚ) 0

/-- A squarefree integer `d ≠ 1` is not a square in `ℚ`. -/
theorem Qsqrt.not_isSquare_of_squarefree {d : ℤ} (hd : Squarefree d) (h1 : d ≠ 1) :
    ¬ IsSquare (d : ℚ) := by
  rintro hsq
  rw [Rat.isSquare_intCast_iff] at hsq
  obtain ⟨m, rfl⟩ := hsq
  have hu : IsUnit m := hd m (dvd_refl _)
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp at h1

instance Qsqrt.fact_not_isSquare {d : ℤ} [hd : Fact (Squarefree d ∧ d ≠ 1)] :
    Fact (¬ IsSquare (d : ℚ)) :=
  ⟨Qsqrt.not_isSquare_of_squarefree hd.out.1 hd.out.2⟩

variable {d : ℤ} [hdsq : Fact (¬ IsSquare (d : ℚ))]

example : Field (Qsqrt d) := inferInstance

instance Qsqrt.instCharZero : CharZero (Qsqrt d) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (Qsqrt d)).injective

instance Qsqrt.instNumberField : NumberField (Qsqrt d) where
  to_finiteDimensional := inferInstance

omit hdsq in
/-- `ℚ(√d)` has degree 2 over `ℚ`. -/
theorem Qsqrt.finrank : Module.finrank ℚ (Qsqrt d) = 2 :=
  QuadraticAlgebra.finrank_eq_two _ _

end ZInQ.Progressions
