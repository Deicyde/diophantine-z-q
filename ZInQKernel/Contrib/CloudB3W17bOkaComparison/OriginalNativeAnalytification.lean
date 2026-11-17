import ZInQKernel.Contrib.CloudB3W17bOkaComparison.GlobalNativeAnalytification
import ZInQKernel.Contrib.CloudB3W17GAGA.CanonicalPointComparison

/-!
# Actual global analytic maps for the ORIGINAL CPts carrier and canonical Hodge atlases

The committed classical topology and choice-based canonical transported atlas
are unchanged. Their PROVED native carrier diffeomorphism carries only the
original MDifferentiability input to the genuine native/Oka construction. The
result is an actual analytic Hom with literal ORIGINAL-point realization;
no topology/model compatibility, GAGA or algebraic map witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

local instance originalPointTopology (X : Over (Spec (CommRingCat.of ℂ))) :
    TopologicalSpace (CloudB3W17Hodge.CPt X) := CloudB3W17Hodge.classicalTopology X

local instance originalPointCharted (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] : ChartedSpace (Fin d → ℂ) (CloudB3W17Hodge.CPt X) :=
  CloudB3W17Hodge.chartedSpace X d

variable (X Y : Over (Spec (CommRingCat.of ℂ))) (d e : ℕ)
variable [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
variable (F : CloudB3W17Hodge.CPt X → CloudB3W17Hodge.CPt Y)
variable (hF : MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) F)

/-- The SAME original point map, read through the PROVED unchanged carrier equivalences. -/
def originalPointMapNative : ComplexPoint X → ComplexPoint Y :=
  fun p => CloudB3W17Hodge.cptEquiv Y (F ((CloudB3W17Hodge.cptEquiv X).symm p))

/-- Original canonical MDifferentiability transports through the ACTUAL proved Cω carrier maps. -/
theorem mdifferentiable_originalPointMapNative
    (hF : MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) F) :
    MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) (originalPointMapNative X Y F) :=
  ((ZInQ.Contrib.CloudB3W17GAGA.contMDiff_cptHomeomorph Y e).mdifferentiable (by simp)).comp
    (hF.comp ((ZInQ.Contrib.CloudB3W17GAGA.contMDiff_cptHomeomorph_symm X d).mdifferentiable (by simp)))

/-- ORIGINAL CPts of the actual analytification, from the genuine closed-point and carrier dictionaries. -/
def originalAnalytificationPoint (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (p : analytification.obj (nativeRelativeDimensionLFT X d)) : CloudB3W17Hodge.CPt X :=
  (CloudB3W17Hodge.cptEquiv X).symm (wholeSchemeNativePoint X d p)

/-- The ACTUAL analytic morphism of the ORIGINAL CPts map in the UNCHANGED canonical Hodge atlas. -/
def originalNativeMDifferentiableAnalytic :
    analytification.obj (nativeRelativeDimensionLFT X d) ⟶
      analytification.obj (nativeRelativeDimensionLFT Y e) :=
  nativeMDifferentiableAnalytic X Y d e (originalPointMapNative X Y F)
    (mdifferentiable_originalPointMapNative X Y d e F hF)

/-- Its actual analytic map realizes the ORIGINAL CPts function, not a replacement point model. -/
theorem originalNativeMDifferentiableAnalytic_points
    (p : analytification.obj (nativeRelativeDimensionLFT X d)) :
    originalAnalytificationPoint Y e ((originalNativeMDifferentiableAnalytic X Y d e F hF).toLRSHom.base p) =
      F (originalAnalytificationPoint X d p) :=
  (congrArg (CloudB3W17Hodge.cptEquiv Y).symm
    (nativeMDifferentiableAnalytic_nativePoint X Y d e (originalPointMapNative X Y F)
      (mdifferentiable_originalPointMapNative X Y d e F hF) p)).trans
    ((CloudB3W17Hodge.cptEquiv Y).symm_apply_apply (F (originalAnalytificationPoint X d p)))

/-- The original canonical native map has an ACTUAL global analytic Hom, without any extra premise. -/
theorem exists_originalNativeMDifferentiableAnalytic
    (hF : MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) F) :
    ∃ f : analytification.obj (nativeRelativeDimensionLFT X d) ⟶
        analytification.obj (nativeRelativeDimensionLFT Y e),
      ∀ p : analytification.obj (nativeRelativeDimensionLFT X d),
        originalAnalytificationPoint Y e (f.toLRSHom.base p) = F (originalAnalytificationPoint X d p) :=
  ⟨originalNativeMDifferentiableAnalytic X Y d e F hF,
    originalNativeMDifferentiableAnalytic_points X Y d e F hF⟩

end ZInQ.Contrib.CloudB3W17bOkaComparison
