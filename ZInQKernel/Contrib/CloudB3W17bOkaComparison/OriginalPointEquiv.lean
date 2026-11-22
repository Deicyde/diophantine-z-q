import ZInQKernel.Contrib.CloudB3W17bOkaComparison.OriginalNativeAnalytification

/-!
# Actual analytification points are precisely the ORIGINAL complex-point carrier

Surjectivity is witnessed by the actual constructed canonical chart centres,
not assumed. Injectivity is the genuine π closed-point theorem. This makes the
original-point realization of the global native analytic morphism explicit
for EVERY original point, not merely points in an unspecified image.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- Every ORIGINAL native complex point has an actual analytification point, the constructed chart centre. -/
theorem wholeSchemeNativePoint_surjective (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] : Function.Surjective (wholeSchemeNativePoint X d) := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  intro p
  refine ⟨wholeSchemeChartCentre X d p, ?_⟩
  apply (nativePointClosedEquiv X).injective
  exact Subtype.ext ((wholeSchemeNativePoint_underlying X d (wholeSchemeChartCentre X d p)).trans
    (wholeSchemeChartCentre_comparison X d p))

/-- Actual analytic points are in genuine bijection with the UNCHANGED native complex points. -/
def nativeAnalytificationPointEquiv (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    analytification.obj (nativeRelativeDimensionLFT X d) ≃ ComplexPoint X :=
  Equiv.ofBijective (wholeSchemeNativePoint X d)
    ⟨wholeSchemeNativePoint_injective X d, wholeSchemeNativePoint_surjective X d⟩

/-- The ORIGINAL complex point map is a bijection, from actual native and original carrier dictionaries. -/
theorem originalAnalytificationPoint_bijective (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] : Function.Bijective (originalAnalytificationPoint X d) :=
  (CloudB3W17Hodge.cptEquiv X).symm.bijective.comp
    ⟨wholeSchemeNativePoint_injective X d, wholeSchemeNativePoint_surjective X d⟩

/-- ACTUAL analytification points in the ORIGINAL CPts carrier, not a substitute model. -/
def originalAnalytificationPointEquiv (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    analytification.obj (nativeRelativeDimensionLFT X d) ≃ CloudB3W17Hodge.CPt X :=
  Equiv.ofBijective (originalAnalytificationPoint X d) (originalAnalytificationPoint_bijective X d)

/-- Original point evaluation of the actual comparison is the literal underlying original scheme point. -/
theorem originalAnalytificationPoint_underlying (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : analytification.obj (nativeRelativeDimensionLFT X d)) :
    (originalAnalytificationPoint X d p).left (IsLocalRing.closedPoint ℂ) =
      (analytificationπ (nativeRelativeDimensionLFT X d)).left.base p :=
  wholeSchemeNativePoint_underlying X d p

local instance originalEquivTopology (X : Over (Spec (CommRingCat.of ℂ))) :
    TopologicalSpace (CloudB3W17Hodge.CPt X) := CloudB3W17Hodge.classicalTopology X

local instance originalEquivCharted (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] : ChartedSpace (Fin d → ℂ) (CloudB3W17Hodge.CPt X) :=
  CloudB3W17Hodge.chartedSpace X d

/-- The actual global analytic Hom realizes the ORIGINAL function at EVERY original CPts point. -/
theorem originalNativeMDifferentiableAnalytic_originalPoint
    (X Y : Over (Spec (CommRingCat.of ℂ))) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (F : CloudB3W17Hodge.CPt X → CloudB3W17Hodge.CPt Y)
    (hF : MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) F) (P : CloudB3W17Hodge.CPt X) :
    originalAnalytificationPoint Y e
      ((originalNativeMDifferentiableAnalytic X Y d e F hF).toLRSHom.base
        ((originalAnalytificationPointEquiv X d).symm P)) = F P :=
  (originalNativeMDifferentiableAnalytic_points X Y d e F hF _).trans
    (congrArg F ((originalAnalytificationPointEquiv X d).apply_symm_apply P))

end ZInQ.Contrib.CloudB3W17bOkaComparison
