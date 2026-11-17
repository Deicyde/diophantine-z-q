/-
Copyright (c) 2026 W17 contributors.
Released under Apache 2.0 license as described in the file LICENSE.

The native projective-space and point definitions are supplied by the Hodge
core port at e222d7ba1999d47ab0618cc0d812bb0b6f8b7229, from
Paul-Lez/HodgeConjecture@2ead713179628a3c738197d5996f51c8a9c886ac.
-/
import ZInQKernel.Contrib.CloudB3W17ProperCompact.ProjectiveChowCover
import ZInQKernel.Contrib.CloudB3W17ProperCompact.PointLift
import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Definitions.AlgebraicGeometry.ComplexPoint.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace W17ProperCompact

/-- The native and FLT degree-zero maps have the same value on every homogeneous polynomial. -/
theorem degreeZeroEquiv_eq (R : Type u) [CommRing R] (n : ℕ) :
    ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) R = (ProjSpace.grad0Equiv R n).symm := by
  apply RingEquiv.ext
  intro p
  rfl

/-- The graded-polynomial bridge lands in the native projective-space over-category. -/
def projSpaceOverIsoNative (R : Type u) [CommRing R] (n : ℕ) :
    Over.mk (ProjSpace.π R n) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec (CommRingCat.of R))) :=
  projSpaceOverIsoTerminal R n

/-- Integral proper schemes have proper surjective covers with actual native projective presentations. -/
theorem exists_projective_surjective_cover {R : Type u} [CommRing R] [IsNoetherianRing R]
    (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [IsIntegral X.left] :
    ∃ (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ X),
      IsProjective Y.hom ∧ IsProper p.left ∧ Surjective p.left := by
  obtain ⟨n, Y, p, i, hp, hs, hi⟩ := exists_native_projective_chow_cover X
  let P : ProjectiveSpace.Presentation Y.hom :=
    { ambientDimension := n
      immersion := i.left
      isClosedImmersion := hi
      immersion_toBase := Over.w i }
  exact ⟨Y, p, ⟨⟨P⟩⟩, hp, hs⟩

/-- The field-valued-point lift is the surjectivity of the native point map. -/
theorem surjective_native_point_map {K : Type} [Field K] [IsAlgClosed K]
    {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] [Surjective f.left] :
    Function.Surjective (Point.map f : Point K X → Point K Y) :=
  surjective_over_points f

/-- A projective Chow projection induces a continuous surjective map on native complex points. -/
theorem exists_projective_continuous_surjective_point_map
    (X : Over (Spec (CommRingCat.of ℂ))) [IsProper X.hom] [IsIntegral X.left] :
    ∃ (Y : Over (Spec (CommRingCat.of ℂ))) (p : Y ⟶ X),
      IsProjective Y.hom ∧
      Continuous (Point.map p : ComplexPoint Y → ComplexPoint X) ∧
      Function.Surjective (Point.map p : ComplexPoint Y → ComplexPoint X) := by
  obtain ⟨Y, p, hY, hp, hs⟩ := exists_projective_surjective_cover X
  have : IsProper p.left := hp
  have : Surjective p.left := hs
  exact ⟨Y, p, hY, Point.continuous_map p, surjective_native_point_map p⟩

end W17ProperCompact
