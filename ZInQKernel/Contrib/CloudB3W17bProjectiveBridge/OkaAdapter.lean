import ZInQKernel.Contrib.CloudB3W17bProjectiveBridge.OkaEmbedding
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.ULiftBase
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.GAGA.ProjectiveDefinition

/-!
# Actual native abelian varieties are projective in Oka's scheme category

The underlying scheme is unchanged. The finite-coordinate comparison is a
proved scheme isomorphism over the genuine lifted complex base; no projectivity
or algebraic-map witness is added as a premise. The Oka projective-space object
is its actual polynomial Proj, not the different W07 relative model by fiat.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ZInQ.Contrib.CloudB3W17bOkaComparison

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bProjectiveBridge

/-- Original A, with only its base spelling changed by the genuine Spec isomorphism. -/
def abVarLiftedLFT (A : PkgI3.AbVar ℂ) : ComplexAnalytic.SchemeLFTℂ.{0} :=
  ⟨overULift A.X, show LocallyOfFiniteType (overULift A.X).hom from inferInstance⟩

@[simp]
theorem abVarLiftedLFT_left (A : PkgI3.AbVar ℂ) : (abVarLiftedLFT A).obj.left = A.X.left := rfl

@[simp]
theorem abVarLiftedLFT_hom (A : PkgI3.AbVar ℂ) :
    (abVarLiftedLFT A).obj.hom = A.X.hom ≫ complexULiftBaseIso.hom := rfl

/-- A×B is the actual native product, not a new independently chosen analytic ambient. -/
def prodAbVarLiftedLFT (A B : PkgI3.AbVar ℂ) : ComplexAnalytic.SchemeLFTℂ.{0} :=
  abVarLiftedLFT (AVGlue.prodAbVar A B)

@[simp]
theorem prodAbVarLiftedLFT_left (A B : PkgI3.AbVar ℂ) :
    (prodAbVarLiftedLFT A B).obj.left = (A.X ⊗ B.X).left := rfl

/-- An actual over-base closed embedding into Oka's projective space exists. -/
theorem abVarLiftedLFT_exists_closed_embedding (A : PkgI3.AbVar ℂ) :
    ∃ (n : ℕ) (i : abVarLiftedLFT A ⟶ ComplexAnalytic.projectiveSpace.{0} n),
      IsClosedImmersion i.hom.left := by
  obtain ⟨n, i, hi⟩ := abVar_exists_oka_over_closed_embedding A
  exact ⟨n, ObjectProperty.homMk i, hi⟩

/-- Oka's original projectivity predicate is proved for the same native A. -/
theorem abVarLiftedLFT_isProjective (A : PkgI3.AbVar ℂ) :
    ComplexAnalytic.IsProjectiveℂ (abVarLiftedLFT A) :=
  abVarLiftedLFT_exists_closed_embedding A

/-- Oka's original projectivity predicate holds for the same native A×B. -/
theorem prodAbVarLiftedLFT_isProjective (A B : PkgI3.AbVar ℂ) :
    ComplexAnalytic.IsProjectiveℂ (prodAbVarLiftedLFT A B) :=
  abVarLiftedLFT_isProjective (AVGlue.prodAbVar A B)

#print axioms abVarLiftedLFT
#print axioms abVarLiftedLFT_left
#print axioms abVarLiftedLFT_hom
#print axioms prodAbVarLiftedLFT
#print axioms prodAbVarLiftedLFT_left
#print axioms polynomialToSpec_eq_oka
#print axioms abVarLiftedLFT_exists_closed_embedding
#print axioms abVarLiftedLFT_isProjective
#print axioms prodAbVarLiftedLFT_isProjective

end ZInQ.Contrib.CloudB3W17bProjectiveBridge
