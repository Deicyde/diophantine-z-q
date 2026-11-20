import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineGammaLRS
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.NativeAffineMapPullback

/-!
# Actual local LRS morphisms for the original native F

The real target-affine Γ pullback is supplied by native MDifferentiability in
the SAME canonical algebraic étale source chart. Coordinate relabelling and
restriction produce the genuine Oka-source Γ map; Γ–Spec then constructs an
actual complex-base-compatible LRS morphism with its full regular pullback law.
No algebraic F/H, GAGA or model-compatibility premise is introduced.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X Y : Over (Spec (CommRingCat.of ℂ))) (d e : ℕ)
variable [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
variable (F : ComplexPoint X → ComplexPoint Y)
variable (hF : MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) F) (p : ComplexPoint X)

/-- The actual source domain in Oka's genuine complex-linear coordinate convention. -/
def nativeMapOkaDomain : Opens (_root_.complexAffineSpace d) :=
  (affineCoordinateULift d).opensCongr (nativeMapAffineDomain X Y d e F hF p)

/-- The actual open Oka source of the original local map. -/
abbrev nativeMapOkaSource : AnalyticSpace := euclideanOpen d (nativeMapOkaDomain X Y d e F hF p)

/-- The actual target-affine regular pullback after genuine coordinate relabelling. -/
def nativeMapOkaRingPullback :
    Γ((nativeMapTargetDatum Y e (F p)).neighborhood.toScheme, ⊤) →+*
      OkaRing (nativeMapOkaDomain X Y d e F hF p) :=
  (OkaRing.congr (affineCoordinateULift d) (nativeMapAffineDomain X Y d e F hF p)).toRingHom.comp
    (nativeMapAffineGammaPullback X Y d e F hF p)

/-- The real Γ map on the same actual Oka-open source. -/
def nativeMapOkaGlobalPullback :
    Γ((nativeMapTargetDatum Y e (F p)).neighborhood.toScheme, ⊤) →+*
      (nativeMapOkaSource X Y d e F hF p).presheaf.obj (op ⊤) :=
  (euclideanSectionToGlobal d (nativeMapOkaDomain X Y d e F hF p)).comp
    (nativeMapOkaRingPullback X Y d e F hF p)

/-- Actual complex constants of the native regular ring pull back to actual Oka constants. -/
theorem nativeMapOkaGlobalPullback_C (c : ℂ) :
    nativeMapOkaGlobalPullback X Y d e F hF p (actualEtaleNativeConst Y e (F p) c) =
      (nativeMapOkaSource X Y d e F hF p).algebraMap c := by
  have h₁ := nativeMapAffineGammaPullback_C X Y d e F hF p c
  have h₂ := (congrArg (fun s => OkaRing.congr (affineCoordinateULift d)
      (nativeMapAffineDomain X Y d e F hF p) s) h₁).trans
    ((OkaRing.congr (affineCoordinateULift d) (nativeMapAffineDomain X Y d e F hF p)).commutes c)
  exact (congrArg (euclideanSectionToGlobal d (nativeMapOkaDomain X Y d e F hF p)) h₂).trans
    (euclideanSectionToGlobal_C d (nativeMapOkaDomain X Y d e F hF p) c)

/-- Actual β as a locally ringed-space morphism to the original target affine scheme. -/
def nativeLocalAffineLRS :
    (nativeMapOkaSource X Y d e F hF p).toLocallyRingedSpace ⟶
      (actualEtaleNativeScheme Y e (F p)).left.toLocallyRingedSpace :=
  actualAffineGammaLRS Y e (F p) (nativeMapOkaSource X Y d e F hF p)
    (nativeMapOkaGlobalPullback X Y d e F hF p)

/-- Actual β, bundled over the actual lifted complex LRS base. -/
def nativeLocalAffineOverLRS :
    AnalyticSpace.toOverSpec.obj (nativeMapOkaSource X Y d e F hF p) ⟶
      Over.mk (overULift (actualEtaleNativeScheme Y e (F p))).hom.toLRSHom :=
  actualAffineGammaOver Y e (F p) (nativeMapOkaSource X Y d e F hF p)
    (nativeMapOkaGlobalPullback X Y d e F hF p) (nativeMapOkaGlobalPullback_C X Y d e F hF p)

/-- This is the actual full Γ pullback, not merely a pointwise or scalar comparison. -/
theorem nativeLocalAffineLRS_gamma_pullback :
    (LocallyRingedSpace.Γ.map (nativeLocalAffineLRS X Y d e F hF p).op).hom =
      nativeMapOkaGlobalPullback X Y d e F hF p :=
  actualAffineGammaLRS_gamma_pullback Y e (F p) (nativeMapOkaSource X Y d e F hF p)
    (nativeMapOkaGlobalPullback X Y d e F hF p)

end ZInQ.Contrib.CloudB3W17bOkaComparison
