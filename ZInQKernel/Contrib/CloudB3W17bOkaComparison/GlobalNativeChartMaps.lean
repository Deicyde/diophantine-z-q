import ZInQKernel.Contrib.CloudB3W17bOkaComparison.WholeSchemeChartCover
import ZInQKernel.Contrib.CloudB3W17bNativeGlue.OriginalPointRealization

/-!
# Actual local maps on shrunk canonical source chart opens

The actual whole-source chart isomorphism is restricted to the true open domain
where the original native F lies in its actual target affine neighbourhood.
All restrictions/lifts are genuine AnalyticSpace.Hom values. Their coordinates
realize the ORIGINAL native point; no compatibility or algebraicity premise.
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

/-- The actual whole-source canonical chart coordinate morphism, into the genuine ℂ^d. -/
def globalNativeChartCoordinates :
    (analytification.obj (nativeRelativeDimensionLFT X d)).restrict (wholeSchemeChartOpen X d p) ⟶
      AnalyticSpace.complexAffineSpace d :=
  (wholeSchemeSourceChartIso X d p).hom ≫ actualChartOpenInclusion X d p

/-- The real preimage of the actual native-F target-affine domain in that source chart. -/
def globalNativeChartDomain :
    Opens ((analytification.obj (nativeRelativeDimensionLFT X d)).restrict (wholeSchemeChartOpen X d p)) :=
  (Opens.map (globalNativeChartCoordinates X d p).toLRSHom.base).obj
    (nativeMapOkaDomain X Y d e F hF p)

/-- The true twice-restricted source inclusion into the whole original analytification. -/
def globalNativeShrunkInclusion :
    ((analytification.obj (nativeRelativeDimensionLFT X d)).restrict (wholeSchemeChartOpen X d p)).restrict
      (globalNativeChartDomain X Y d e F hF p) ⟶ analytification.obj (nativeRelativeDimensionLFT X d) :=
  ((analytification.obj (nativeRelativeDimensionLFT X d)).restrict (wholeSchemeChartOpen X d p)).ofRestrict
      (globalNativeChartDomain X Y d e F hF p) ≫
    (analytification.obj (nativeRelativeDimensionLFT X d)).ofRestrict (wholeSchemeChartOpen X d p)

/-- This actual source inclusion is a genuine open immersion. -/
instance globalNativeShrunkInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (globalNativeShrunkInclusion X Y d e F hF p).toLRSHom := by
  let A := analytification.obj (nativeRelativeDimensionLFT X d)
  let M := wholeSchemeChartOpen X d p
  let U := globalNativeChartDomain X Y d e F hF p
  haveI h₁ : LocallyRingedSpace.IsOpenImmersion
      ((A.restrict M).toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) :=
    LocallyRingedSpace.isOpenImmersion_ofRestrict _ _
  haveI h₂ : LocallyRingedSpace.IsOpenImmersion (A.toLocallyRingedSpace.ofRestrict M.isOpenEmbedding) :=
    LocallyRingedSpace.isOpenImmersion_ofRestrict _ _
  exact LocallyRingedSpace.IsOpenImmersion.comp
    ((A.restrict M).toLocallyRingedSpace.ofRestrict U.isOpenEmbedding)
    (A.toLocallyRingedSpace.ofRestrict M.isOpenEmbedding)

/-- The ACTUAL shrunk source chart open of the whole original analytification. -/
def globalNativeShrunkOpen : Opens (analytification.obj (nativeRelativeDimensionLFT X d)) :=
  analyticOpenImage (globalNativeShrunkInclusion X Y d e F hF p)

/-- The ACTUAL map from the shrunk whole-source open to the actual native-F Euclidean domain. -/
def globalNativeChartMap :
    (analytification.obj (nativeRelativeDimensionLFT X d)).restrict (globalNativeShrunkOpen X Y d e F hF p) ⟶
      nativeMapOkaSource X Y d e F hF p :=
  (analyticOpenImageIso (globalNativeShrunkInclusion X Y d e F hF p)).inv ≫
    AnalyticSpace.restrictHom (globalNativeChartCoordinates X d p) (nativeMapOkaDomain X Y d e F hF p)

/-- The actual chart map's coordinate inclusion square, not an assumed commuting diagram. -/
theorem globalNativeChartMap_fac :
    globalNativeChartMap X Y d e F hF p ≫
      (AnalyticSpace.complexAffineSpace d).ofRestrict (nativeMapOkaDomain X Y d e F hF p) =
    (analyticOpenImageIso (globalNativeShrunkInclusion X Y d e F hF p)).inv ≫
      ((analytification.obj (nativeRelativeDimensionLFT X d)).restrict (wholeSchemeChartOpen X d p)).ofRestrict
        (globalNativeChartDomain X Y d e F hF p) ≫ globalNativeChartCoordinates X d p :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f => (analyticOpenImageIso (globalNativeShrunkInclusion X Y d e F hF p)).inv ≫ f)
      (AnalyticSpace.restrictHom_fac (globalNativeChartCoordinates X d p) (nativeMapOkaDomain X Y d e F hF p)))

/-- Its actual coordinate tuple is the unchanged canonical source chart coordinate tuple. -/
theorem globalNativeChartMap_coordinates
    (x : (analytification.obj (nativeRelativeDimensionLFT X d)).restrict (globalNativeShrunkOpen X Y d e F hF p)) :
    ((globalNativeChartMap X Y d e F hF p).toLRSHom.base x).1 =
      (((wholeSchemeSourceChartIso X d p).hom.toLRSHom.base
        (((analyticOpenImageIso (globalNativeShrunkInclusion X Y d e F hF p)).inv.toLRSHom.base x).1)).1) :=
  congrArg (fun f : (analytification.obj (nativeRelativeDimensionLFT X d)).restrict
      (globalNativeShrunkOpen X Y d e F hF p) ⟶ AnalyticSpace.complexAffineSpace d => f.toLRSHom.base x)
    (globalNativeChartMap_fac X Y d e F hF p)

/-- The actual shrunk chart coordinates realize the ORIGINAL native point of the whole comparison. -/
theorem globalNativeChartMap_realization
    (x : (analytification.obj (nativeRelativeDimensionLFT X d)).restrict (globalNativeShrunkOpen X Y d e F hF p)) :
    (nativeMapSourceChart X d p).symm
      ((affineCoordinateULift d).symm (((globalNativeChartMap X Y d e F hF p).toLRSHom.base x).1)) =
        wholeSchemeNativePoint X d x.1 := by
  let v := (analyticOpenImageIso (globalNativeShrunkInclusion X Y d e F hF p)).inv.toLRSHom.base x
  have hv : v.1.1 = x.1 :=
    congrArg (fun f : (analytification.obj (nativeRelativeDimensionLFT X d)).restrict
        (globalNativeShrunkOpen X Y d e F hF p) ⟶ analytification.obj (nativeRelativeDimensionLFT X d) =>
      f.toLRSHom.base x) (analyticOpenImageIso_inv_fac (globalNativeShrunkInclusion X Y d e F hF p))
  exact (congrArg (fun w : ULift.{0} (Fin d) → ℂ =>
      (nativeMapSourceChart X d p).symm ((affineCoordinateULift d).symm w))
        (globalNativeChartMap_coordinates X Y d e F hF p x)).trans
    ((wholeSchemeSourceChartIso_realization X d p v.1).trans (congrArg (wholeSchemeNativePoint X d) hv))

/-- The original target affine neighbourhood actually contains the original F(p). -/
theorem nativeMapTargetOpen_mem_centre (Y' : Over (Spec (CommRingCat.of ℂ))) (e' : ℕ)
    [SmoothOfRelativeDimension e' Y'.hom] (q : ComplexPoint Y') :
    q ∈ Point.overOpen (nativeMapTargetOpen Y' e' q) := by
  change q.underlying ∈ (nativeMapTargetDatum Y' e' q).ambientCoordinateOpen
  simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top]
    using (nativeMapTargetDatum Y' e' q).mem

/-- Every actual source point lies in the actual shrunk chart at its ORIGINAL native centre. -/
theorem globalNativeShrunkOpen_mem_self (z : analytification.obj (nativeRelativeDimensionLFT X d)) :
    z ∈ globalNativeShrunkOpen X Y d e F hF (wholeSchemeNativePoint X d z) := by
  let p := wholeSchemeNativePoint X d z
  let M := wholeSchemeChartOpen X d p
  let q : (analytification.obj (nativeRelativeDimensionLFT X d)).restrict M :=
    ⟨z, wholeSchemeChart_mem_self X d z⟩
  let w := (wholeSchemeSourceChartIso X d p).hom.toLRSHom.base q
  have hpoint : (nativeMapSourceChart X d p).symm ((affineCoordinateULift d).symm w.1) = p :=
    wholeSchemeSourceChartIso_realization X d p q
  have hdomain : q ∈ globalNativeChartDomain X Y d e F hF p := by
    change (affineCoordinateULift d).symm w.1 ∈ nativeMapAffineDomain X Y d e F hF p
    refine ⟨w.2, ?_⟩
    exact (congrArg (fun p' : ComplexPoint X => F p' ∈ Point.overOpen (nativeMapTargetOpen Y e (F p))) hpoint).mpr
      (nativeMapTargetOpen_mem_centre Y e (F p))
  exact ⟨⟨q, hdomain⟩, rfl⟩

/-- The actual shrunk source opens form a genuine cover of the whole original analytification. -/
theorem globalNativeShrunkOpens_cover :
    ∀ z : analytification.obj (nativeRelativeDimensionLFT X d), ∃ p : ComplexPoint X,
      z ∈ globalNativeShrunkOpen X Y d e F hF p :=
  fun z => ⟨wholeSchemeNativePoint X d z, globalNativeShrunkOpen_mem_self X Y d e F hF z⟩

end ZInQ.Contrib.CloudB3W17bOkaComparison
