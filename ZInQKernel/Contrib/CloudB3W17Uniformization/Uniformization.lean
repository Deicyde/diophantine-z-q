import ZInQKernel.Contrib.CloudB3W17Uniformization.AbelianAnalyticAssembly
import ZInQKernel.Contrib.CloudB3W17Hodge.CptManifold

/-!
# Unconditional exact H103 uniformization

For every actual `PkgI3.AbVar ℂ`, use the proved native dimensions, unchanged
canonical complex-point topology/atlas, transported analytic manifold theorem,
regular Γ coordinates/maps and compactness/connectedness to apply the actual
commutative analytic exponential/full-lattice torus theorem. This proves the
original BP coordinate-form statement with no additional open leaf.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace CloudB3W17Uniformization

set_option autoImplicit false

/-- The original uniformization statement for every genuine complex abelian variety. -/
theorem uniformizationLeafAll : BPAnalytic.Uniformization.UniformizationLeafAll := by
  intro A
  obtain ⟨g, n, hg, hn⟩ := exists_nativeRelativeDimensions A
  have := hg
  have := hn
  let : TopologicalSpace (CloudB3W17Hodge.CPt A.X) := CloudB3W17Hodge.classicalTopology A.X
  let : TopologicalSpace (CloudB3W17Hodge.CPt (A.X ⊗ A.X)) :=
    CloudB3W17Hodge.classicalTopology (A.X ⊗ A.X)
  let : ChartedSpace (Fin g → ℂ) (CloudB3W17Hodge.CPt A.X) :=
    CloudB3W17Hodge.chartedSpace A.X g
  let : ChartedSpace (Fin n → ℂ) (CloudB3W17Hodge.CPt (A.X ⊗ A.X)) :=
    CloudB3W17Hodge.chartedSpace (A.X ⊗ A.X) n
  have : IsManifold 𝓘(ℂ, Fin g → ℂ) ω (CloudB3W17Hodge.CPt A.X) :=
    CloudB3W17Hodge.isManifold_cpt A.X g
  have : IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CloudB3W17Hodge.CPt (A.X ⊗ A.X)) :=
    CloudB3W17Hodge.isManifold_cpt (A.X ⊗ A.X) n
  exact uniformizationLeaf_of_canonicalAtlas A g n

end CloudB3W17Uniformization
