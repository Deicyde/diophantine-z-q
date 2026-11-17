import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Descent of finite linear systems

A field embedding admits a linear retraction after the larger field is viewed as a
vector space over the smaller field. Applying that retraction to each coordinate
of a solution descends every finite linear system. Only the column index needs
to be finite; the row index may be arbitrary, and either index may be empty.
-/

open scoped BigOperators Matrix

namespace FiniteLinearDescent

variable {K L I J : Type*} [Field K] [Field L] [Fintype J]

/-- A linear system with coefficients and right-hand side in a field has a
solution in that field whenever it has a solution after a field extension. -/
theorem exists_solution_of_field_extension
    (φ : K →+* L) (A : Matrix I J K) (b : I → K)
    {x : J → L} (hx : A.map φ *ᵥ x = φ ∘ b) :
    ∃ y : J → K, A *ᵥ y = b := by
  classical
  let : Algebra K L := φ.toAlgebra
  let f : K →ₗ[K] L := Algebra.linearMap K L
  have hf : LinearMap.ker f = ⊥ := by
    apply LinearMap.ker_eq_bot'.2
    intro a ha
    change φ a = 0 at ha
    by_contra h
    have hzero : (1 : L) = 0 := by
      calc
        (1 : L) = φ (a⁻¹ * a) := by rw [inv_mul_cancel₀ h, φ.map_one]
        _ = φ a⁻¹ * φ a := φ.map_mul _ _
        _ = 0 := by rw [ha, mul_zero]
    exact one_ne_zero hzero
  obtain ⟨p, hp⟩ := f.exists_leftInverse_of_injective hf
  have hpφ (a : K) : p (φ a) = a := by
    have h := DFunLike.congr_fun hp a
    change p (φ a) = a at h
    exact h
  have hpmul (a : K) (z : L) : p (φ a * z) = a * p z := by
    change p (a • z) = a • p z
    exact p.map_smul a z
  refine ⟨fun j => p (x j), ?_⟩
  funext i
  have hi := congrFun hx i
  change (∑ j, φ (A i j) * x j) = φ (b i) at hi
  calc
    (A *ᵥ fun j => p (x j)) i = ∑ j, A i j * p (x j) := rfl
    _ = p (∑ j, φ (A i j) * x j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact (hpmul (A i j) (x j)).symm
    _ = p (φ (b i)) := congrArg p hi
    _ = b i := hpφ (b i)

/-- Solvability of a finite linear system is invariant under a field extension. -/
theorem solvable_field_extension_iff
    (φ : K →+* L) (A : Matrix I J K) (b : I → K) :
    (∃ x : J → L, A.map φ *ᵥ x = φ ∘ b) ↔
      ∃ y : J → K, A *ᵥ y = b := by
  constructor
  · rintro ⟨x, hx⟩
    exact exists_solution_of_field_extension φ A b hx
  · rintro ⟨y, hy⟩
    refine ⟨φ ∘ y, ?_⟩
    funext i
    calc
      (A.map φ *ᵥ (φ ∘ y)) i = φ ((A *ᵥ y) i) :=
        (φ.map_mulVec A y i).symm
      _ = φ (b i) := congrArg φ (congrFun hy i)

/-- A system with coefficients in a subfield descends from the ambient field.
In particular, the ambient field may be the complex numbers. -/
theorem exists_solution_subfield
    (F : Subfield L) (A : Matrix I J F) (b : I → F)
    {x : J → L} (hx : A.map F.subtype *ᵥ x = fun i => (b i : L)) :
    ∃ y : J → F, A *ᵥ y = b := by
  exact exists_solution_of_field_extension F.subtype A b hx

end FiniteLinearDescent
