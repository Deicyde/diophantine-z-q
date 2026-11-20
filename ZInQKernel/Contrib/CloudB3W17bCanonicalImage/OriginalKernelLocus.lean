import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AbVarNativeAnalytification
import ZInQKernel.Contrib.CloudB3W17bIdentity.PulledIdentity

/-!
# Vanishing of the actual identity ideal pulled back through the SAME original H

The actual global morphism is exactly the published factory at prodAbVar/H.
The identity ideal, its coherence and range are the existing identity/analytic-ideal
suppliers. Original point equality is reflected by their proved closed-point law.
No analytic/algebraic replacement H, point dictionary, or GAGA premise is supplied.
-/

open CategoryTheory AlgebraicGeometry ComplexAnalytic TopologicalSpace
open scoped Manifold ContDiff Topology CategoryTheory.MonObj
open PkgI3 (AbVar)
open ZInQ.Contrib.CloudB3W17GAGA (APts)
open ZInQ.Contrib.CloudB3W17bOkaComparison
open ZInQ.Contrib.CloudB3W17bAnalyticIdeal
open ZInQ.Contrib.CloudB3W17bIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section
namespace ZInQ.Contrib.CloudB3W17bCanonicalImage

local instance originalKernelIntegral (A : AbVar ℂ) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
local instance originalKernelTopology (A : AbVar ℂ) : TopologicalSpace (APts A) :=
  CloudB3W17Hodge.classicalTopology A.X
local instance originalKernelCharted (A : AbVar ℂ) :
    ChartedSpace (Fin (TopologicalSpace.dim A.X.left) → ℂ) (APts A) :=
  CloudB3W17Hodge.chartedSpace A.X (TopologicalSpace.dim A.X.left)

local instance originalKernelProductGeomInt (A B : AbVar ℂ) :
    GeometricallyIntegral (AVGlue.prodAbVar A B).X.hom := AbVar.geomInt (AVGlue.prodAbVar A B)
local instance originalKernelProductIntegral (A B : AbVar ℂ) :
    IsIntegral (AVGlue.prodAbVar A B).X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton (AVGlue.prodAbVar A B).X.hom
local instance originalKernelProductSmooth (A B : AbVar ℂ) :
    Smooth (AVGlue.prodAbVar A B).X.hom := AbVar.smooth (AVGlue.prodAbVar A B)
local instance originalKernelProductTopology (A B : AbVar ℂ) :
    TopologicalSpace (APts (AVGlue.prodAbVar A B)) :=
  CloudB3W17Hodge.classicalTopology (AVGlue.prodAbVar A B).X
local instance originalKernelProductCharted (A B : AbVar ℂ) :
    ChartedSpace (Fin (TopologicalSpace.dim (AVGlue.prodAbVar A B).X.left) → ℂ)
      (APts (AVGlue.prodAbVar A B)) :=
  CloudB3W17Hodge.chartedSpace (AVGlue.prodAbVar A B).X
    (TopologicalSpace.dim (AVGlue.prodAbVar A B).X.left)

/-- The pulled identity ideal through the actual H is coherent, on the actual source. -/
theorem isCoherent_actual_originalKernelIdeal (A B : AbVar ℂ)
    (H : APts (AVGlue.prodAbVar A B) →* APts B)
    (hH : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim (AVGlue.prodAbVar A B).X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω H) :
    (pulledIdeal (identitySection B)
      (abVarAnalyticOfOriginalContMDiff (AVGlue.prodAbVar A B) B H hH).toLRSHom).IsCoherent :=
  isCoherent_pulledIdentityIdeal B _

/-- The actual pulled identity ideal vanishes precisely on the SAME original H=1
under the proved actual analytic/original-point equivalence. -/
theorem vanishingLocus_actual_originalKernelIdeal (A B : AbVar ℂ)
    (H : APts (AVGlue.prodAbVar A B) →* APts B)
    (hH : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim (AVGlue.prodAbVar A B).X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω H) :
    vanishingLocus (invImageIdealι
        (abVarAnalyticOfOriginalContMDiff (AVGlue.prodAbVar A B) B H hH).toLRSHom
        (closedIdealι (analytification.map (identitySection B)).toLRSHom)) =
      {x | H (abVarAnalytificationPoints (AVGlue.prodAbVar A B) x) = 1} := by
  rw [vanishingLocus_pulledIdeal, range_analytification_identitySection_eq_points]
  ext x
  have hp : abVarAnalytificationPoints B
      ((abVarAnalyticOfOriginalContMDiff (AVGlue.prodAbVar A B) B H hH).toLRSHom.base x) =
      H (abVarAnalytificationPoints (AVGlue.prodAbVar A B) x) := by
    simpa only [Equiv.symm_apply_apply] using
      abVarAnalyticOfOriginalContMDiff_apply (AVGlue.prodAbVar A B) B H hH
        (abVarAnalytificationPoints (AVGlue.prodAbVar A B) x)
  change abVarAnalytificationPoints B
      ((abVarAnalyticOfOriginalContMDiff (AVGlue.prodAbVar A B) B H hH).toLRSHom.base x) = 1 ↔ _
  rw [hp]; rfl

end ZInQ.Contrib.CloudB3W17bCanonicalImage
