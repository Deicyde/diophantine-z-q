import ZInQKernel.Contrib.CloudB3W17bProjectiveBridge.NativeEmbedding
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.ULiftBase

/-! Exact base and original-point controls for the native embedding construction.
No analytic chart, Oka projectivity assumption or alternative point carrier is
used to construct the closed embedding. -/

open CategoryTheory AlgebraicGeometry MvPolynomial MonoidalCategory
open ZInQ.Contrib.CloudB3W17bOkaComparison

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bProjectiveBridge

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual original A, viewed over the actual lifted base, embeds in polynomial Proj.
Both the source point carrier and the scheme morphism retain the original scheme. -/
theorem abVar_overULift_polynomial_embedding (A : PkgI3.AbVar ℂ) :
    ∃ (n : ℕ) (e : (overULift A.X).left ⟶ Proj (homogeneousSubmodule (Fin (n+1)) (ULift.{0} ℂ))),
      IsClosedImmersion e ∧ e ≫ Proj.projectiveSpaceOverAffineToSpec (Fin (n+1)) (ULift.{0} ℂ) =
        (overULift A.X).hom :=
  abVar_polynomial_embedding A complexULiftBaseIso

/-- The actual product source is preserved after the same base wrapper. -/
theorem prodAbVar_overULift_polynomial_embedding (A B : PkgI3.AbVar ℂ) :
    ∃ (n : ℕ) (e : (overULift (A.X ⊗ B.X)).left ⟶
        Proj (homogeneousSubmodule (Fin (n+1)) (ULift.{0} ℂ))),
      IsClosedImmersion e ∧ e ≫ Proj.projectiveSpaceOverAffineToSpec (Fin (n+1)) (ULift.{0} ℂ) =
        (overULift (A.X ⊗ B.X)).hom :=
  prodAbVar_polynomial_embedding A B complexULiftBaseIso

/-- Base rebinding changes the point parameter only by the genuine Spec isomorphism.
Composing with an actual embedding preserves the same closed scheme-point image. -/
theorem lifted_embedding_point_underlying (X : Over (Spec (.of ℂ)))
    {n : ℕ} (e : X.left ⟶ Proj (homogeneousSubmodule (Fin (n+1)) (ULift.{0} ℂ)))
    (p : ComplexPoint X) :
    (complexULiftBaseIso.inv ≫ p.left ≫ e) (IsLocalRing.closedPoint (ULift.{0} ℂ)) =
      e p.underlying := by
  change e (p.left (complexULiftBaseIso.inv (IsLocalRing.closedPoint (ULift.{0} ℂ)))) =
    e (p.left (IsLocalRing.closedPoint ℂ))
  congr 2
  exact Subsingleton.elim (α := Spec (.of ℂ)) _ _

/-- The scalar/base comparison is the actual ULift coefficient ring isomorphism. -/
theorem lifted_complex_base_map :
    complexULiftBaseIso.hom = Spec.map (CommRingCat.ofHom (ULift.ringEquiv (R := ℂ)).toRingHom) :=
  rfl

#print axioms abVar_overULift_polynomial_embedding
#print axioms prodAbVar_overULift_polynomial_embedding
#print axioms lifted_embedding_point_underlying
#print axioms lifted_complex_base_map

end ZInQ.Contrib.CloudB3W17bProjectiveBridge
