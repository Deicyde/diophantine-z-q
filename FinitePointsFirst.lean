import Mathlib

/-!
# Finiteness of algebra maps to finite coefficient rings

Finite-type algebra generators determine an algebra map. A finite target
therefore admits only finitely many such maps. The argument uses algebra
finite type, not module finiteness, and retains the actual homomorphisms.
-/

noncomputable section
set_option autoImplicit false

namespace SemistableGeometry.FinitePoints

/-- The actual algebra-homomorphism type is finite when the source is finite type and the target is finite. -/
theorem finite_algHom_of_finiteType
    (R S T : Type) [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Algebra R S] [Algebra R T] [Algebra.FiniteType R S] [Finite T] : Finite (S →ₐ[R] T) := by
  classical
  obtain ⟨s, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial.mp
    (inferInstance : Algebra.FiniteType R S)
  let v : (S →ₐ[R] T) → ({x : S // x ∈ s} → T) := fun g i ↦ g (f (MvPolynomial.X i))
  apply Finite.of_injective v
  intro g h he
  have hc : g.comp f = h.comp f := by
    apply MvPolynomial.algHom_ext
    intro i
    exact congrFun he i
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := hf x
  exact congrArg (fun q : MvPolynomial {x : S // x ∈ s} R →ₐ[R] T ↦ q p) hc

end SemistableGeometry.FinitePoints
