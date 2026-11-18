import ZInQKernel.Contrib.CloudR2Hom.C4SourcePort.ProjectiveEmbedding
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.FiniteSet

/-!
# The projective affine-open coverage needed by the stabilizer quotient

This thin H72 bridge reuses H70 C4's ACTUAL closed projective embedding and the
already-published native W07 homogeneous-prime-avoidance proof. No new Stacks
source is acquired/copied/vendored, and no affine-coverage input is assumed.
Import the C4 source directly, avoiding unrelated B4/Leray assembly dependencies.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L4

/-- Typed affine-open wiring for an actual closed projective embedding. -/
theorem finiteSet_affineOpen_of_closedEmbedding
    {k : Type} [Field k] {X : Scheme} {coordinates : Type}
    (embedding : X ⟶ ℙ(coordinates; Spec (.of k))) [IsClosedImmersion embedding]
    (E : Set X) (hE : E.Finite) :
    ∃ O : X.Opens, IsAffineOpen O ∧ E ⊆ O :=
  exists_isAffineOpen_superset_of_isClosedImmersion embedding E hE

/-- Every finite set of points of the original actual abelian variety lies in an affine open. -/
theorem abVar_finiteSet_affineOpen {k : Type} [Field k] (A : PkgI3.AbVar k)
    (E : Set A.X.left) (hE : E.Finite) :
    ∃ O : A.X.left.Opens, IsAffineOpen O ∧ E ⊆ O := by
  obtain ⟨coordinates, finiteCoordinates, embedding, closed, over⟩ :=
    ZInQ.Contrib.CloudR2Hom.C4SourcePort.exists_closedImmersion_projectiveSpace A
  haveI := finiteCoordinates
  haveI := closed
  exact finiteSet_affineOpen_of_closedEmbedding embedding E hE

end ZInQ.Contrib.CloudR2Poincare.L4
