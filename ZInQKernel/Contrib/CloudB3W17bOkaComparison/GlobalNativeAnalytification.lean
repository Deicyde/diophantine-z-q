import ZInQKernel.Contrib.CloudB3W17bOkaComparison.GlobalNativeChartMaps

/-!
# The actual global analytic morphism of the ORIGINAL native manifold map

All source chart isomorphisms, their actual open cover, shrunk chart maps,
pointwise reducedness and original-point realization are constructed internally.
The real Oka opens-cover gluing theorem is applied to those proved data. The
only map regularity input is MDifferentiability in the unchanged canonical
Hodge atlas. No algebraic map, GAGA or model compatibility witness is assumed.
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
variable (hF : MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) F)

/-- The ACTUAL global analytic morphism induced by the ORIGINAL native canonical manifold map. -/
def nativeMDifferentiableAnalytic :
    analytification.obj (nativeRelativeDimensionLFT X d) ⟶
      analytification.obj (nativeRelativeDimensionLFT Y e) :=
  ZInQ.Contrib.CloudB3W17bNativeGlue.nativeGlobalAnalyticOfMaps X Y d e F hF
    (fun p : ComplexPoint X => p) (globalNativeShrunkOpen X Y d e F hF)
    (globalNativeShrunkOpens_cover X Y d e F hF) (wholeSchemeAnalytification_pointwiseReduced X d)
    (globalNativeChartMap X Y d e F hF) (wholeSchemeNativePoint X d)
    (fun p z hz => globalNativeChartMap_realization X Y d e F hF p ⟨z, hz⟩)

/-- The actual global comparison realizes EVERY original native point value of F. -/
theorem nativeMDifferentiableAnalytic_comparison
    (z : analytification.obj (nativeRelativeDimensionLFT X d)) :
    ((nativeMDifferentiableAnalytic X Y d e F hF).toLRSHom ≫
      (analytificationπ (nativeRelativeDimensionLFT Y e)).left).base z =
        (F (wholeSchemeNativePoint X d z)).underlying :=
  ZInQ.Contrib.CloudB3W17bNativeGlue.nativeGlobalAnalyticOfMaps_base X Y d e F hF
    (fun p : ComplexPoint X => p) (globalNativeShrunkOpen X Y d e F hF)
    (globalNativeShrunkOpens_cover X Y d e F hF) (wholeSchemeAnalytification_pointwiseReduced X d)
    (globalNativeChartMap X Y d e F hF) (wholeSchemeNativePoint X d)
    (fun p z hz => globalNativeChartMap_realization X Y d e F hF p ⟨z, hz⟩) z

/-- The ORIGINAL native-point map of this actual analytic morphism is literally F. -/
theorem nativeMDifferentiableAnalytic_nativePoint
    (z : analytification.obj (nativeRelativeDimensionLFT X d)) :
    wholeSchemeNativePoint Y e ((nativeMDifferentiableAnalytic X Y d e F hF).toLRSHom.base z) =
      F (wholeSchemeNativePoint X d z) := by
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth e Y.hom
  apply (nativePointClosedEquiv Y).injective
  exact Subtype.ext
    ((wholeSchemeNativePoint_underlying Y e ((nativeMDifferentiableAnalytic X Y d e F hF).toLRSHom.base z)).trans
      (nativeMDifferentiableAnalytic_comparison X Y d e F hF z))

/-- Existence of an ACTUAL analytic Hom with ORIGINAL-point realization, with no extra premise. -/
theorem exists_nativeMDifferentiableAnalytic
    (hF : MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) F) :
    ∃ f : analytification.obj (nativeRelativeDimensionLFT X d) ⟶
        analytification.obj (nativeRelativeDimensionLFT Y e),
      ∀ z : analytification.obj (nativeRelativeDimensionLFT X d),
        wholeSchemeNativePoint Y e (f.toLRSHom.base z) = F (wholeSchemeNativePoint X d z) :=
  ⟨nativeMDifferentiableAnalytic X Y d e F hF, nativeMDifferentiableAnalytic_nativePoint X Y d e F hF⟩

end ZInQ.Contrib.CloudB3W17bOkaComparison
