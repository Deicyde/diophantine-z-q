import ZInQKernel.Contrib.CloudB3W17bNativeGlue.NativeMapGlue
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.NativeLocalAnalyticMaps
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineComparisonPoints
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.ActualChartInverse

/-!
# Original point realisation of the actual local maps, and their global gluing

The actual local analytic maps `nativeLocalAnalytic` (constructed, read-only, from the
original native `F` and its proved full Γ pullback) are shown to realise the original
native points: the comparison point of `β` at `w` is the underlying scheme point of
`F (chart⁻¹ w)`.  The proof computes the intrinsic values of the actual Γ pullback
(literal holomorphic evaluation on the Euclidean source) and identifies the actual
comparison point through the already proved `affineComparisonPoint` dictionary.

Then, for ANY analytic space `A` with an actual open cover `M i` and actual
isomorphisms `A|M i ≅ nativeMapOkaSource … (c i)` (input data: the source chart
isomorphisms are constructed elsewhere) whose coordinates realise a point map
`Ψ : A → ComplexPoint X`, the local maps glue, by the actual `glueMorphismsOfOpens`,
to a unique analytic map `A ⟶ Y^an` realising `F ∘ Ψ`.  Nothing about algebraicity of
`F`, GAGA, or compatibility of models is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic
open scoped Manifold ContDiff Topology
open ZInQ.Contrib.CloudB3W17bOkaComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bNativeGlue

variable (X Y : Over (Spec (CommRingCat.of ℂ))) (d e : ℕ)
variable [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
variable (F : ComplexPoint X → ComplexPoint Y)
variable (hF : MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) F) (p : ComplexPoint X)

local instance nativeGlueTargetAlgebra :
    Algebra ℂ Γ((nativeMapTargetDatum Y e (F p)).neighborhood.toScheme, ⊤) :=
  (nativeMapTargetDatum Y e (F p)).coordinateRingComplexAlgebra

local instance nativeGlueComparisonAlgebra :
    Algebra ℂ Γ((actualEtaleNativeScheme Y e (F p)).left, ⊤) :=
  (actualEtaleDatum Y e (F p)).coordinateRingComplexAlgebra

/-- The actual affine-domain coordinate of a point of the Euclidean Oka source. -/
def nativeOkaSourceCoord (w : nativeMapOkaSource X Y d e F hF p) :
    nativeMapAffineDomain X Y d e F hF p :=
  ⟨(affineCoordinateULift d).symm w.1, w.2⟩

/-- **Intrinsic values of the actual Γ pullback** are the original native regular values at
the actual target point. -/
theorem nativeMapOkaGlobalPullback_intrinsicEval (w : nativeMapOkaSource X Y d e F hF p)
    (r : Γ((nativeMapTargetDatum Y e (F p)).neighborhood.toScheme, ⊤)) :
    intrinsicEval (nativeMapOkaSource X Y d e F hF p) (U := ⊤) w trivial
        (nativeMapOkaGlobalPullback X Y d e F hF p r) =
      (nativeMapTargetDatum Y e (F p)).pointAlgHomHomeomorph
        (nativeMapTargetPoint X Y d e F hF p (nativeOkaSourceCoord X Y d e F hF p w)) r :=
  (intrinsicEval_open d (nativeMapOkaDomain X Y d e F hF p) w ⊤ trivial _).trans rfl

/-- **The actual comparison point of `β` is the original native target point.** -/
theorem nativeLocalAffine_comparisonPoint (w : nativeMapOkaSource X Y d e F hF p) :
    affineComparisonPoint Y e (F p) (nativeMapOkaSource X Y d e F hF p)
        (nativeLocalAffineLRS X Y d e F hF p)
        (actualAffineGammaLRS_over Y e (F p) (nativeMapOkaSource X Y d e F hF p)
          (nativeMapOkaGlobalPullback X Y d e F hF p)
          (nativeMapOkaGlobalPullback_C X Y d e F hF p)) w =
      nativeMapTargetPoint X Y d e F hF p (nativeOkaSourceCoord X Y d e F hF p w) := by
  apply (nativeMapTargetDatum Y e (F p)).pointAlgHomHomeomorph.injective
  rw [affineComparisonPoint, Homeomorph.apply_symm_apply]
  apply AlgHom.ext
  intro r
  change intrinsicEval (nativeMapOkaSource X Y d e F hF p) (U := ⊤) w trivial
      ((LocallyRingedSpace.Γ.map (nativeLocalAffineLRS X Y d e F hF p).op).hom r) = _
  rw [nativeLocalAffineLRS_gamma_pullback]
  exact nativeMapOkaGlobalPullback_intrinsicEval X Y d e F hF p w r

/-- The actual LRS map `β` sends `w` to the underlying point of the native target point. -/
theorem nativeLocalAffineLRS_base (w : nativeMapOkaSource X Y d e F hF p) :
    (nativeLocalAffineLRS X Y d e F hF p).base w =
      (nativeMapTargetPoint X Y d e F hF p (nativeOkaSourceCoord X Y d e F hF p w)).underlying :=
  (affineComparisonPoint_underlying Y e (F p) (nativeMapOkaSource X Y d e F hF p)
      (nativeLocalAffineLRS X Y d e F hF p)
      (actualAffineGammaLRS_over Y e (F p) (nativeMapOkaSource X Y d e F hF p)
        (nativeMapOkaGlobalPullback X Y d e F hF p)
        (nativeMapOkaGlobalPullback_C X Y d e F hF p)) w).symm.trans
    (congrArg Point.underlying (nativeLocalAffine_comparisonPoint X Y d e F hF p w))

/-- **Original point realisation of the actual local analytic map** into `Y^an`: its comparison
point at `w` is the underlying scheme point of `F (chart⁻¹ w)`. -/
theorem nativeLocalAnalytic_comparison_base (w : nativeMapOkaSource X Y d e F hF p) :
    ((nativeLocalAnalytic X Y d e F hF p).toLRSHom ≫
        (analytificationπ (nativeRelativeDimensionLFT Y e)).left).base w =
      (F ((nativeMapSourceChart X d p).symm ((affineCoordinateULift d).symm w.1))).underlying := by
  unfold nativeLocalAnalytic
  rw [comparison_comp_map_base, nativeLocalAffineAnalytic_fac]
  refine (congrArg _ (nativeLocalAffineLRS_base X Y d e F hF p w)).trans ?_
  have hq : Point.map (ComplexPoint.openInclusion Y (nativeMapTargetDatum Y e (F p)).neighborhood)
      (nativeMapTargetPoint X Y d e F hF p (nativeOkaSourceCoord X Y d e F hF p w)) =
      F ((nativeMapSourceChart X d p).symm ((affineCoordinateULift d).symm w.1)) :=
    congrArg Subtype.val ((ComplexPoint.openHomeomorph Y
      (nativeMapTargetDatum Y e (F p)).neighborhood).apply_symm_apply _)
  exact (Point.underlying_map _ _).symm.trans (congrArg Point.underlying hq)

/-! ### Global gluing along actual source charts -/

variable {A : AnalyticSpace.{0}} {ι : Type} (c : ι → ComplexPoint X) (M : ι → A.Opens)
  (hM : ∀ x : A, ∃ i, x ∈ M i)
  (eiso : ∀ i, A.restrict (M i) ≅ nativeMapOkaSource X Y d e F hF (c i))
  (Ψ : A → ComplexPoint X)

/-- The point law needed by `chartGlue`, from the chart realisation of `Ψ`. -/
theorem nativeLocal_point_law
    (hchart : ∀ i (x : A) (hx : x ∈ M i),
      (nativeMapSourceChart X d (c i)).symm
        ((affineCoordinateULift d).symm ((eiso i).hom.toLRSHom.base ⟨x, hx⟩).1) = Ψ x)
    (i : ι) (x : A) (hx : x ∈ M i) :
    ((nativeLocalAnalytic X Y d e F hF (c i)).toLRSHom ≫
        (analytificationπ (nativeRelativeDimensionLFT Y e)).left).base
        ((eiso i).hom.toLRSHom.base ⟨x, hx⟩) = (F (Ψ x)).underlying := by
  rw [nativeLocalAnalytic_comparison_base, hchart]

/-- **The global analytic map** `A ⟶ Y^an` glued from the actual local maps. -/
def nativeGlobalAnalytic
    (hchart : ∀ i (x : A) (hx : x ∈ M i),
      (nativeMapSourceChart X d (c i)).symm
        ((affineCoordinateULift d).symm ((eiso i).hom.toLRSHom.base ⟨x, hx⟩).1) = Ψ x) :
    A ⟶ analytification.obj (nativeRelativeDimensionLFT Y e) :=
  chartGlue M hM (fun i => nativeMapOkaSource X Y d e F hF (c i)) eiso
    (fun i => euclideanOpen_pointwiseReduced d (nativeMapOkaDomain X Y d e F hF (c i)))
    (fun i => nativeLocalAnalytic X Y d e F hF (c i)) (fun x => (F (Ψ x)).underlying)
    (nativeLocal_point_law X Y d e F hF c M eiso Ψ hchart)

/-- It restricts on each chart to the actual local map. -/
theorem ofRestrict_comp_nativeGlobalAnalytic
    (hchart : ∀ i (x : A) (hx : x ∈ M i),
      (nativeMapSourceChart X d (c i)).symm
        ((affineCoordinateULift d).symm ((eiso i).hom.toLRSHom.base ⟨x, hx⟩).1) = Ψ x)
    (i : ι) :
    A.ofRestrict (M i) ≫ nativeGlobalAnalytic X Y d e F hF c M hM eiso Ψ hchart =
      (eiso i).hom ≫ nativeLocalAnalytic X Y d e F hF (c i) :=
  ofRestrict_comp_chartGlue M hM _ eiso _ _ _ _ i

/-- **Original point realisation**: the glued map's actual comparison point at `x` is the
underlying scheme point of `F (Ψ x)`. -/
theorem nativeGlobalAnalytic_base
    (hchart : ∀ i (x : A) (hx : x ∈ M i),
      (nativeMapSourceChart X d (c i)).symm
        ((affineCoordinateULift d).symm ((eiso i).hom.toLRSHom.base ⟨x, hx⟩).1) = Ψ x)
    (x : A) :
    ((nativeGlobalAnalytic X Y d e F hF c M hM eiso Ψ hchart).toLRSHom ≫
        (analytificationπ (nativeRelativeDimensionLFT Y e)).left).base x = (F (Ψ x)).underlying :=
  chartGlue_base M hM _ eiso _ _ _ _ x

/-- Uniqueness among maps restricting to the actual local maps. -/
theorem nativeGlobalAnalytic_unique
    (hchart : ∀ i (x : A) (hx : x ∈ M i),
      (nativeMapSourceChart X d (c i)).symm
        ((affineCoordinateULift d).symm ((eiso i).hom.toLRSHom.base ⟨x, hx⟩).1) = Ψ x)
    (ψ : A ⟶ analytification.obj (nativeRelativeDimensionLFT Y e))
    (hψ : ∀ i, A.ofRestrict (M i) ≫ ψ = (eiso i).hom ≫ nativeLocalAnalytic X Y d e F hF (c i)) :
    ψ = nativeGlobalAnalytic X Y d e F hF c M hM eiso Ψ hchart :=
  chartGlue_unique M hM _ eiso _ _ _ _ ψ hψ

/-- Uniqueness among maps realising `F ∘ Ψ` on points (rigidity). -/
theorem nativeGlobalAnalytic_unique_of_base
    (hchart : ∀ i (x : A) (hx : x ∈ M i),
      (nativeMapSourceChart X d (c i)).symm
        ((affineCoordinateULift d).symm ((eiso i).hom.toLRSHom.base ⟨x, hx⟩).1) = Ψ x)
    (ψ : A ⟶ analytification.obj (nativeRelativeDimensionLFT Y e))
    (hψ : ∀ x : A, (ψ.toLRSHom ≫ (analytificationπ (nativeRelativeDimensionLFT Y e)).left).base x =
      (F (Ψ x)).underlying) :
    ψ = nativeGlobalAnalytic X Y d e F hF c M hM eiso Ψ hchart :=
  chartGlue_unique_of_base M hM _ eiso _ _ _ _ ψ hψ

/-! ### Global gluing from local chart MAPS out of a pointwise-reduced source -/

section OfMaps

variable {A : AnalyticSpace.{0}} {ι : Type} (c : ι → ComplexPoint X) (M : ι → A.Opens)
  (hM : ∀ x : A, ∃ i, x ∈ M i) (hA : PointwiseReduced A)
  (φ : ∀ i, A.restrict (M i) ⟶ nativeMapOkaSource X Y d e F hF (c i))
  (Ψ : A → ComplexPoint X)

/-- The point law for the composites `φ i ≫ β`, from the coordinate realisation of `Ψ`. -/
theorem nativeLocal_point_law_ofMaps
    (hchart : ∀ i (x : A) (hx : x ∈ M i),
      (nativeMapSourceChart X d (c i)).symm
        ((affineCoordinateULift d).symm ((φ i).toLRSHom.base ⟨x, hx⟩).1) = Ψ x)
    (i : ι) (x : A) (hx : x ∈ M i) :
    ((φ i ≫ nativeLocalAnalytic X Y d e F hF (c i)).toLRSHom ≫
        (analytificationπ (nativeRelativeDimensionLFT Y e)).left).base ⟨x, hx⟩ =
      (F (Ψ x)).underlying := by
  change ((nativeLocalAnalytic X Y d e F hF (c i)).toLRSHom ≫
      (analytificationπ (nativeRelativeDimensionLFT Y e)).left).base
      ((φ i).toLRSHom.base ⟨x, hx⟩) = _
  rw [nativeLocalAnalytic_comparison_base, hchart]

/-- **The global analytic map** glued from `φ i ≫ β (c i)` over a pointwise-reduced source
(e.g. one covered by the actual source chart isomorphisms, via `pointwiseReduced_of_charts`
and `euclideanOpen_pointwiseReduced`). -/
def nativeGlobalAnalyticOfMaps
    (hchart : ∀ i (x : A) (hx : x ∈ M i),
      (nativeMapSourceChart X d (c i)).symm
        ((affineCoordinateULift d).symm ((φ i).toLRSHom.base ⟨x, hx⟩).1) = Ψ x) :
    A ⟶ analytification.obj (nativeRelativeDimensionLFT Y e) :=
  reducedGlue M hM hA (fun i => φ i ≫ nativeLocalAnalytic X Y d e F hF (c i))
    (fun x => (F (Ψ x)).underlying) (nativeLocal_point_law_ofMaps X Y d e F hF c M φ Ψ hchart)

theorem ofRestrict_comp_nativeGlobalAnalyticOfMaps
    (hchart : ∀ i (x : A) (hx : x ∈ M i),
      (nativeMapSourceChart X d (c i)).symm
        ((affineCoordinateULift d).symm ((φ i).toLRSHom.base ⟨x, hx⟩).1) = Ψ x) (i : ι) :
    A.ofRestrict (M i) ≫ nativeGlobalAnalyticOfMaps X Y d e F hF c M hM hA φ Ψ hchart =
      φ i ≫ nativeLocalAnalytic X Y d e F hF (c i) :=
  ofRestrict_comp_reducedGlue M hM hA _ _ _ i

theorem nativeGlobalAnalyticOfMaps_base
    (hchart : ∀ i (x : A) (hx : x ∈ M i),
      (nativeMapSourceChart X d (c i)).symm
        ((affineCoordinateULift d).symm ((φ i).toLRSHom.base ⟨x, hx⟩).1) = Ψ x) (x : A) :
    ((nativeGlobalAnalyticOfMaps X Y d e F hF c M hM hA φ Ψ hchart).toLRSHom ≫
        (analytificationπ (nativeRelativeDimensionLFT Y e)).left).base x = (F (Ψ x)).underlying :=
  reducedGlue_base M hM hA _ _ _ x

theorem nativeGlobalAnalyticOfMaps_unique_of_base
    (hchart : ∀ i (x : A) (hx : x ∈ M i),
      (nativeMapSourceChart X d (c i)).symm
        ((affineCoordinateULift d).symm ((φ i).toLRSHom.base ⟨x, hx⟩).1) = Ψ x)
    (ψ : A ⟶ analytification.obj (nativeRelativeDimensionLFT Y e))
    (hψ : ∀ x : A, (ψ.toLRSHom ≫ (analytificationπ (nativeRelativeDimensionLFT Y e)).left).base x =
      (F (Ψ x)).underlying) :
    ψ = nativeGlobalAnalyticOfMaps X Y d e F hF c M hM hA φ Ψ hchart :=
  reducedGlue_unique_of_base M hM hA _ _ _ ψ hψ

end OfMaps

/-! ### Pointwise reducedness from the actual source chart isomorphisms -/

/-- The actual chart branch of the analytified affine chart is pointwise reduced, through the
actual source chart isomorphism `actualChartIso` onto the Euclidean Oka source. -/
theorem actualChartBranch_pointwiseReduced (Xs : Over (Spec (CommRingCat.of ℂ))) (n : ℕ)
    [SmoothOfRelativeDimension n Xs.hom] (z : ComplexPoint Xs) :
    PointwiseReduced ((actualChartAnalytification Xs n z).restrict (actualChartBranch Xs n z)) :=
  PointwiseReduced.of_iso (actualChartIso Xs n z)
    (euclideanOpen_pointwiseReduced n (actualEtaleOkaOpen Xs n z))

/-- Hence the analytified affine chart is pointwise reduced at every point of its branch. -/
theorem actualChartAnalytification_pointwiseReducedAt (Xs : Over (Spec (CommRingCat.of ℂ)))
    (n : ℕ) [SmoothOfRelativeDimension n Xs.hom] (z : ComplexPoint Xs)
    (x : actualChartAnalytification Xs n z) (hx : x ∈ actualChartBranch Xs n z) :
    PointwiseReducedAt (actualChartAnalytification Xs n z) x :=
  pointwiseReducedAt_of_restrict (actualChartBranch Xs n z) ⟨x, hx⟩
    (actualChartBranch_pointwiseReduced Xs n z ⟨x, hx⟩)

end ZInQ.Contrib.CloudB3W17bNativeGlue
