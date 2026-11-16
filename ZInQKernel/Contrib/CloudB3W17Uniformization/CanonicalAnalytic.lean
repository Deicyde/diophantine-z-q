import ZInQKernel.Contrib.CloudB3W17Uniformization.TransportAnalytic
import ZInQKernel.Contrib.CloudB3W17GAGA.CanonicalPointComparison

/-!
# Canonical CPt analyticity from the proved atlas comparison

These wrappers discharge the comparison argument of `TransportAnalytic` using
the actual compiled `cptDiffeomorph`, for the unchanged Bridge classical topology
and choice-based charted space. No analytic dictionary premise remains.
The independent IsManifold transport is supplied separately in final assembly.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory AlgebraicGeometry

namespace CloudB3W17Uniformization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CloudB3W17Hodge ZInQ.Contrib.CloudB3W17GAGA

local instance (X : Over (Spec ↧ℂ)) : TopologicalSpace (CPt X) := classicalTopology X
noncomputable local instance (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    ChartedSpace (Fin d → ℂ) (CPt X) := chartedSpace X d

/-- Actual CPt regular sections are holomorphic in the canonical transported atlas. -/
theorem contMDiffOn_canonicalEvaluate (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : X.left.Opens) (s : Γ(X.left, U)) :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω (XevalAt X U s) {P : CPt X | XPtIn X P U} :=
  contMDiffOn_cptEvaluate X d (cptDiffeomorph X d) (cptDiffeomorph_apply X d) U s

/-- Actual CPt Γ-defined coordinates are local analytic diffeomorphisms. -/
theorem canonical_regularCoordinates (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (P : CPt X) :
    ∃ (U : X.left.Opens) (f : Fin d → Γ(X.left, U)), XPtIn X P U ∧
      IsLocalDiffeomorphAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
        (fun Q i => XevalAt X U (f i) Q) P :=
  cpt_regularCoordinates X d (cptDiffeomorph X d) (cptDiffeomorph_apply X d) P

/-- Actual complex-point maps of scheme morphisms are globally analytic. -/
theorem contMDiff_canonicalMap (X Y : Over (Spec ↧ℂ)) (d m : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension m Y.hom] (α : X ⟶ Y) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin m → ℂ) ω (fun P : CPt X => P ≫ α) :=
  contMDiff_cptMap X d (cptDiffeomorph X d) (cptDiffeomorph_apply X d) m
    (cptDiffeomorph Y m) (cptDiffeomorph_apply Y m) α

end CloudB3W17Uniformization
