import ZInQKernel.Contrib.CloudR2Poincare.L4.QuotientDescent
import ZInQKernel.Contrib.CloudR2Poincare.L2.SeesawFiniteness

/-!
# B3's literal quotient consumer interface

Agreed with L2 through the H72 lead. This file only STATES the internal B3
output telescope. It supplies no existence Fact or unproved geometric instance.
`FiniteStabilizerQuotientExists` (imported from `QuotientDescent`) is the
separately labelled upstream quotient-existence input; (A) is the explicit
`ReducedGlobalNormalizedSeesaw` argument below.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L4

/-- The exact B3 output consumed by the B4 graph/PolarizationRetract assembly.
Its existence is not asserted by this interface declaration. -/
def StabilizerAbVarQuotientExists : Prop :=
  ∀ (hA : L2.ReducedGlobalNormalizedSeesaw) {k : Type} [Field k] [CharZero k]
    (B : PkgI3.AbVar k) (M : B.X.left.Modules) (hM : L2.VeryAmple B.X.hom M),
    letI : M.IsInvertible := hM.isInvertible
    ∃ (H : L1.FiniteStabilizerScheme B (Scheme.Pic.mk M))
      (Q : PkgI3.AbVar k) (q : PkgI3.AbVar.Hom B Q),
      Flat q.hom.left ∧ IsFinite q.hom.left ∧ Surjective q.hom.left ∧
      LocallyOfFinitePresentation q.hom.left ∧
      IsPullback ((fst H.K B.X ≫ H.j) * snd H.K B.X) (snd H.K B.X) q.hom q.hom ∧
      Q.dim = B.dim

end ZInQ.Contrib.CloudR2Poincare.L4
