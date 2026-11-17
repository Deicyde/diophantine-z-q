import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineRingMorphism
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.NativeLocalLRS

/-!
# Actual local Oka analytic morphisms for the original native F

The genuine constant-compatible local LRS/Γ map is constructed in NativeLocalLRS.
The ACTUAL analytification UP lifts it to β, retaining the original native
source chart and target scheme. No algebraic F/H or compatibility witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- The ORIGINAL relatively smooth scheme is LFT internally, not an additional hypothesis. -/
def nativeRelativeDimensionLFT (Y : Over (Spec (CommRingCat.of ℂ))) (e : ℕ)
    [SmoothOfRelativeDimension e Y.hom] : SchemeLFTℂ := by
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth e Y.hom
  exact nativeSchemeLFT Y

@[simp]
theorem nativeRelativeDimensionLFT_left (Y : Over (Spec (CommRingCat.of ℂ))) (e : ℕ)
    [SmoothOfRelativeDimension e Y.hom] : (nativeRelativeDimensionLFT Y e).obj.left = Y.left := rfl

variable (X Y : Over (Spec (CommRingCat.of ℂ))) (d e : ℕ)
variable [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
variable (F : ComplexPoint X → ComplexPoint Y)
variable (hF : MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) F) (p : ComplexPoint X)

/-- The ACTUAL analytic local map β to the ORIGINAL target affine analytification. -/
def nativeLocalAffineAnalytic :
    nativeMapOkaSource X Y d e F hF p ⟶ analytification.obj (actualEtaleSchemeLFT Y e (F p)) :=
  actualAffineGammaAnalytic Y e (F p) (nativeMapOkaSource X Y d e F hF p)
    (nativeMapOkaGlobalPullback X Y d e F hF p) (nativeMapOkaGlobalPullback_C X Y d e F hF p)

/-- The actual local map to the ORIGINAL whole target's true analytification. -/
def nativeLocalAnalytic :
    nativeMapOkaSource X Y d e F hF p ⟶ analytification.obj (nativeRelativeDimensionLFT Y e) := by
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth e Y.hom
  exact nativeLocalAffineAnalytic X Y d e F hF p ≫
    analytification.map (nativeSchemeLFTMap
      (ComplexPoint.openInclusion Y (nativeMapTargetDatum Y e (F p)).neighborhood))

/-- The true comparison is exactly the constructed native regular-ring LRS pullback. -/
theorem nativeLocalAffineAnalytic_fac :
    (nativeLocalAffineAnalytic X Y d e F hF p).toLRSHom ≫
      (analytificationπ (actualEtaleSchemeLFT Y e (F p))).left =
      nativeLocalAffineLRS X Y d e F hF p :=
  actualAffineGammaAnalytic_fac Y e (F p) (nativeMapOkaSource X Y d e F hF p)
    (nativeMapOkaGlobalPullback X Y d e F hF p) (nativeMapOkaGlobalPullback_C X Y d e F hF p)

/-- The actual analytic local map keeps the proved full native Γ pullback law. -/
theorem nativeLocalAffineAnalytic_gamma_pullback :
    (LocallyRingedSpace.Γ.map
      ((nativeLocalAffineAnalytic X Y d e F hF p).toLRSHom ≫
        (analytificationπ (actualEtaleSchemeLFT Y e (F p))).left).op).hom =
      nativeMapOkaGlobalPullback X Y d e F hF p := by
  rw [nativeLocalAffineAnalytic_fac]
  exact nativeLocalAffineLRS_gamma_pullback X Y d e F hF p

end ZInQ.Contrib.CloudB3W17bOkaComparison
