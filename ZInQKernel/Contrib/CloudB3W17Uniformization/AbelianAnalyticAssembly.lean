import ZInQKernel.Contrib.CloudB3W17Uniformization.FromAnalyticPoints
import ZInQKernel.Contrib.CloudB3W17Uniformization.AbelianPointLieGroup
import ZInQKernel.Contrib.CloudB3W17Uniformization.CanonicalAnalytic
import ZInQKernel.Contrib.CloudB3W17Uniformization.ClassicalNeighborhood
import ZInQKernel.Contrib.CloudB3W17Uniformization.NativeAbelianGeometry
import ZInQKernel.Contrib.CloudB3W17ProperCompact.AbVarCompact

/-!
# Pointwise H103 assembly in the genuine canonical complex-point atlas

All regular-function, morphism, topology, compactness, connectedness and torus
inputs are supplied by proved W17 sources. This intermediate assembly has only
the usual Mathlib `IsManifold` assumptions for the factor and product's canonical
transported atlases; the Hodge atlas supplier fills those in the final theorem.
It is not an open-leaf replacement or a closing claim by itself.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace CloudB3W17Uniformization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open PkgI3 (AbVar)
open CloudB3W17Hodge

local instance (X : Over (Spec ↧ℂ)) : TopologicalSpace (CPt X) := classicalTopology X
noncomputable local instance (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] : ChartedSpace (Fin d → ℂ) (CPt X) := chartedSpace X d

/-- Every remaining pointwise component of H103 is assembled from actual donor theorems. -/
theorem uniformizationLeaf_of_canonicalAtlas (A : AbVar ℂ) (g n : ℕ)
    [SmoothOfRelativeDimension g A.X.hom] [SmoothOfRelativeDimension n (A.X ⊗ A.X).hom]
    [IsManifold 𝓘(ℂ, Fin g → ℂ) ω (CPt A.X)]
    [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CPt (A.X ⊗ A.X))] :
    BPAnalytic.Uniformization.UniformizationLeaf A := by
  have : CompactSpace (ComplexPoint A.X) := W17ProperCompact.compactSpace_complexPoint_abVar A
  have : ConnectedSpace (ComplexPoint A.X) := native_connectedSpace_abVar A
  have : CompactSpace (CPt A.X) := (cptHomeomorph A.X).symm.compactSpace
  have : ConnectedSpace (CPt A.X) := (cptHomeomorph A.X).connectedSpace_iff.mpr inferInstance
  have : LieGroup 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ) := lieGroup_of_analyticRegularMaps A g n
    (fun α => contMDiff_canonicalMap A.X A.X g g α)
    (fun α => contMDiff_canonicalMap (A.X ⊗ A.X) A.X n g α)
    (fun α => contMDiff_canonicalMap A.X (A.X ⊗ A.X) g n α)
  exact uniformizationLeaf_of_analyticPoints A g
    (fun U => isOpen_cptIn A.X U)
    (fun U f => contMDiffOn_canonicalEvaluate A.X g U f)
    (canonical_regularCoordinates A.X g)
    (fun P₀ N hN => regular_neighborhood_basis P₀ N hN)

end CloudB3W17Uniformization
