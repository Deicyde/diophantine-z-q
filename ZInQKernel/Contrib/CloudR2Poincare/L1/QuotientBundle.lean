import ZInQKernel.Contrib.CloudR2Poincare.L1.DualInterface
import ZInQKernel.Contrib.CloudR2Poincare.L1.Normalization
import ZInQKernel.Contrib.CloudR2Poincare.L1.PicardDescent

/-!
# The normalized polarization bundle on an actual stabilizer quotient

This is Milne AVs §10's DESCENT step, conditional only on an actual finite
stabilizer scheme / quotient and the relation's compatibility with the
normalized bundle class. It does NOT assume that the quotient is a dual or
that any general Picard functor is scheme-representable.

The output is an actual invertible sheaf on A×(A/K(L)), with normalization
and the required pullback class. Establishing Pic⁰ universality of this
candidate bundle (the graph/ZMT step) is still separate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry
open scoped MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L1

open Scheme

/-- Descend the normalized Mumford polarization family to the actual finite-flat quotient.
All scheme-representability requirements remain in the explicit quotient data,
not in a desired Pic⁰/dual Fact. -/
theorem exists_quotientPolarizationBundle
    {k : Type u} [Field k] (A : _root_.PkgI3.AbVar k) (L : A.X.left.Pic)
    (H : FiniteStabilizerScheme A L) (Q : StabilizerQuotient A L H)
    (hcompat :
      (picardFunctor A.X.hom).obj.map (((fst H.K A.X ≫ H.j) * snd H.K A.X).op)
          ((toPicardFunctor A.X.hom).app (.op A.X)
            (normalizedPolarizationFamily A.X L (𝟙 A.X))) =
        (picardFunctor A.X.hom).obj.map (snd H.K A.X).op
          ((toPicardFunctor A.X.hom).app (.op A.X)
            (normalizedPolarizationFamily A.X L (𝟙 A.X)))) :
    ∃ (P : (pullback A.X.hom Q.Q.hom).Modules) (hP : P.IsInvertible),
      IsNormalizedFamily A Q.Q (@Pic.mk _ P hP) ∧
      Pic.map (JacobianChallenge.baseChangeMap A.X.hom Q.q) (@Pic.mk _ P hP) =
        normalizedPolarizationFamily A.X L (𝟙 A.X) := by
  obtain ⟨Pclass, hnormalized, hpullback⟩ := exists_normalizedPicardClass_descent A.X.hom
    η[A.X].left (abVarUnit_over A) Q.q ((fst H.K A.X ≫ H.j) * snd H.K A.X)
    (snd H.K A.X) Q.kernelPair (normalizedPolarizationFamily A.X L (𝟙 A.X))
    (normalizedPolarizationFamily_normalized A.X L (𝟙 A.X)) hcompat
  let P := (fromSkeleton (pullback A.X.hom Q.Q.hom).Modules).obj Pclass.val
  haveI : P.IsInvertible := Pic.isInvertible Pclass
  refine ⟨P, inferInstance, ?_, ?_⟩
  · change Pic.map (sectionBaseChange A.X.hom η[A.X].left (abVarUnit_over A) Q.Q)
      (Pic.mk P) = 1
    rw [Pic.mk_fromSkeleton]
    exact hnormalized
  · rw [Pic.mk_fromSkeleton]
    exact hpullback

end ZInQ.Contrib.CloudR2Poincare.L1
