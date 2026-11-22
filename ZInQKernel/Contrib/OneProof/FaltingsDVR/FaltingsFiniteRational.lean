import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! A locally finite type scheme over an algebraically closed field with finitely many
rational points has finitely many scheme points. -/

noncomputable section

set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace ZInQ.FaltingsRestate
universe u

/-- Finite rational points over an algebraically closed field give finite
underlying scheme points, by the Jacobson property. -/
theorem finite_of_finite_rational_points
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom]
    [Finite ((𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ X)] : Finite X.left := by
  let S := Spec (CommRingCat.of k)
  let e := pointEquivClosedPoint X.hom
  let f : ((𝟙_ (Over S)) ⟶ X) → closedPoints X.left :=
    fun p => e ⟨p.left, Over.w p⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨p, hp⟩ := e.surjective x
    exact ⟨Over.homMk p.1 p.2, hp⟩
  haveI : Finite (closedPoints X.left) := Finite.of_surjective f hf
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hFin : (closedPoints X.left).Finite := Set.toFinite _
  have hCl : IsClosed (closedPoints X.left) := by
    rw [← (closedPoints X.left).biUnion_of_singleton]
    exact hFin.isClosed_biUnion fun _ hx => hx
  have hCeq : closure (closedPoints X.left) = Set.univ := closure_closedPoints
  rw [hCl.closure_eq] at hCeq
  exact Set.finite_univ_iff.mp (hCeq ▸ hFin)

end ZInQ.FaltingsRestate
