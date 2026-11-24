import ZInQKernel.Contrib.CloudR2Poincare.L4.FiniteSum
import ZInQKernel.Contrib.CloudR2Poincare.L4.DimensionFiniteType
import ZInQKernel.Contrib.CloudR2Poincare.L4.ProductDimension

/-!
# The exact H-72 complement isogeny obligation

H-72 round 2, lane L4. The sum map is the literal `fst ≫ i * snd ≫ g`
from the lead's fixed statement. Its actual scheme-theoretic kernel is
finite; properness then gives finiteness of the sum. The rational-unit
product local-ring calculation supplies the product-dimension lower bound.
The finite image is closed, and a closed subset of the irreducible
finite-dimensional target with full dimension is the whole target.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option linter.style.haveILetI false

/-- The exact `ComplementIsogeny` obligation, with no additional assumptions. -/
theorem ComplementIsogeny_proof : ZInQ.Contrib.CloudR2Poincare.ComplementIsogeny := by
  intro k _ _ J B Z D i g φ _ hgi hg hf hJD hDB
  haveI : IsFinite (fst B.X Z.X ≫ i.hom * snd B.X Z.X ≫ g.hom).left :=
    finite_sum_abVar J B Z D i g φ hgi hg hf.1
  haveI : IsIntegral J.X.left := GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
  haveI : CompactSpace J.X.left := QuasiCompact.compactSpace_of_compactSpace J.X.hom
  refine ⟨inferInstance,
    surjective_of_isFinite_of_topologicalKrullDim_le _ (scheme_dimension_ne_top J.X.hom) ?_⟩
  change J.dim ≤ topologicalKrullDim (B.X ⊗ Z.X).left
  calc
    J.dim ≤ Z.dim + D.dim := hJD
    _ ≤ Z.dim + B.dim := add_le_add le_rfl hDB
    _ = B.dim + Z.dim := add_comm _ _
    _ ≤ topologicalKrullDim (B.X ⊗ Z.X).left := product_dimension_lower_bound B Z

end ZInQ.Contrib.CloudR2Poincare.L4
