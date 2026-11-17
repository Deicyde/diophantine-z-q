import ZInQKernel.Contrib.CloudB3W17bProjectiveBridge.LiftedEmbedding
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AlgebraicGeometry.ProjectiveSpace.Basic

/-! Closed embeddings in the actual polynomial projective-space object used by
Oka, with the unchanged native source schemeleft and genuine ULift base map. -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ZInQ.Contrib.CloudB3W17bOkaComparison

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bProjectiveBridge

/-- W07's polynomial-Proj structure map equals Oka's actual toSpec map. -/
theorem polynomialToSpec_eq_oka (n : ℕ) (R : Type) [CommRing R] :
    Proj.projectiveSpaceOverAffineToSpec (Fin (n+1)) R =
      CloudB3W17bOkaProjectiveSpace.toSpec n R :=
  coefficientStructureMap_eq (Fin (n+1)) R

/-- The actual original A over the lifted complex base embeds in Oka's actual projective space. -/
theorem abVar_exists_oka_over_closed_embedding (A : PkgI3.AbVar ℂ) :
    ∃ (n : ℕ) (i : overULift A.X ⟶
        Over.mk (CloudB3W17bOkaProjectiveSpace.toSpec n (ULift.{0} ℂ))),
      IsClosedImmersion i.left := by
  obtain ⟨n, e, he, hb⟩ := abVar_overULift_polynomial_embedding A
  have hbase : e ≫ CloudB3W17bOkaProjectiveSpace.toSpec n (ULift.{0} ℂ) =
      (overULift A.X).hom := by
    rw [← polynomialToSpec_eq_oka]
    exact hb
  exact ⟨n, Over.homMk e hbase, he⟩

/-- The same original A×B scheme over the lifted base has the same actual embedding. -/
theorem prodAbVar_exists_oka_over_closed_embedding (A B : PkgI3.AbVar ℂ) :
    ∃ (n : ℕ) (i : overULift (A.X ⊗ B.X) ⟶
        Over.mk (CloudB3W17bOkaProjectiveSpace.toSpec n (ULift.{0} ℂ))),
      IsClosedImmersion i.left :=
  abVar_exists_oka_over_closed_embedding (AVGlue.prodAbVar A B)


end ZInQ.Contrib.CloudB3W17bProjectiveBridge
