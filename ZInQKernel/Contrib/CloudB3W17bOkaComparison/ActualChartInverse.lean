import ZInQKernel.Contrib.CloudB3W17bOkaComparison.ActualBranchMaps
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.CanonicalEtaleUniqueness

/-!
# Actual analytic isomorphism of the original canonical étale inverse chart

The constructed reverse coordinates and α have the true polynomial-base square
and the same ORIGINAL native regular residue values. The genuine OPEN algebraic
unramified diagonal then gives equality of the actual LRS comparison maps;
analytification UP injectivity gives the actual AS identity. No local-model,
GAGA, algebraic F/H, Henselianity or compatibility witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (p : ComplexPoint X)

set_option maxHeartbeats 1200000 in
/-- Reverse coordinates followed by α have the actual original affine-scheme comparison map. -/
theorem actualChartReverse_comparison :
    (actualChartReverse X d p ≫ affineChartAnalytic X d p).toLRSHom ≫ actualChartComparison X d p =
      ((actualChartAnalytification X d p).ofRestrict (actualChartBranch X d p)).toLRSHom ≫
        actualChartComparison X d p := by
  let Z := actualChartAnalytification X d p
  let S := Z.restrict (actualChartBranch X d p)
  let π := actualChartComparison X d p
  let F : S ⟶ Z := actualChartReverse X d p ≫ affineChartAnalytic X d p
  let G : S ⟶ Z := Z.ofRestrict (actualChartBranch X d p)
  let D := actualEtaleDatum X d p
  let μ := actualEtaleOkaGlobalPullback X d p
  have hc (a : S ⟶ Z) (c : ℂ) :
      (LocallyRingedSpace.Γ.map (a.toLRSHom ≫ π).op).hom
        (D.coordinateRingHomOnOpen (MvPolynomial.C c)) = S.algebraMap c :=
    (LocallyRingedSpace.Γ_map_comp_apply a.toLRSHom π _).trans
      ((congrArg (LocallyRingedSpace.Γ.map a.toLRSHom.op).hom
        (affineComparison_gamma_constants X d p Z π (actualChartComparison_over X d p) c)).trans
          (a.isCLinear c))
  have hcoords : (LocallyRingedSpace.Γ.map (F.toLRSHom ≫ π).op).hom.comp D.coordinateRingHomOnOpen =
      (LocallyRingedSpace.Γ.map (G.toLRSHom ≫ π).op).hom.comp D.coordinateRingHomOnOpen := by
    apply MvPolynomial.ringHom_ext
    · intro c
      exact (hc F c).trans (hc G c).symm
    · intro i
      let r : Γ((actualEtaleNativeScheme X d p).left, ⊤) :=
        D.coordinateRingHomOnOpen (MvPolynomial.X i)
      let j : ULift.{0} (Fin d) := ULift.up i
      let τ := actualChartReverse X d p
      let α := affineChartAnalytic X d p
      let I := actualChartOpenInclusion X d p
      calc
        (LocallyRingedSpace.Γ.map (F.toLRSHom ≫ π).op).hom r =
            (LocallyRingedSpace.Γ.map (τ.toLRSHom ≫ (α.toLRSHom ≫ π)).op).hom r :=
          congrArg (fun f : S.toLocallyRingedSpace ⟶
              (actualEtaleNativeScheme X d p).left.toLocallyRingedSpace =>
            (LocallyRingedSpace.Γ.map f.op).hom r) (Category.assoc _ _ _)
        _ = (LocallyRingedSpace.Γ.map τ.toLRSHom.op).hom
            ((LocallyRingedSpace.Γ.map (α.toLRSHom ≫ π).op).hom r) :=
          LocallyRingedSpace.Γ_map_comp_apply _ _ _
        _ = (LocallyRingedSpace.Γ.map τ.toLRSHom.op).hom (μ r) :=
          congrArg (LocallyRingedSpace.Γ.map τ.toLRSHom.op).hom
            (RingHom.congr_fun (affineChartAnalytic_gamma_pullback X d p) r)
        _ = (LocallyRingedSpace.Γ.map τ.toLRSHom.op).hom (AnalyticSpace.coordPullback I j) :=
          congrArg (LocallyRingedSpace.Γ.map τ.toLRSHom.op).hom
            (actualEtaleOkaGlobalPullback_coordinate X d p j)
        _ = AnalyticSpace.coordPullback (τ ≫ I) j :=
          (AnalyticSpace.coordPullback_comp τ I j).symm
        _ = AnalyticSpace.coordPullback (G ≫ actualChartCoordinates X d p) j :=
          congrArg (fun a : S ⟶ AnalyticSpace.complexAffineSpace d => AnalyticSpace.coordPullback a j)
            (actualChartReverse_fac X d p)
        _ = (LocallyRingedSpace.Γ.map G.toLRSHom.op).hom
            (actualChartCoordinateSections X d p j) :=
          (AnalyticSpace.coordPullback_comp G (actualChartCoordinates X d p) j).trans
            (congrArg (LocallyRingedSpace.Γ.map G.toLRSHom.op).hom (actualChartCoordinates_pullback X d p j))
        _ = (LocallyRingedSpace.Γ.map (G.toLRSHom ≫ π).op).hom r :=
          (LocallyRingedSpace.Γ_map_comp_apply G.toLRSHom π r).symm
  have hv (a : S ⟶ Z) (x : S) (r : Γ((actualEtaleNativeScheme X d p).left, ⊤)) :
      intrinsicEval S (U := ⊤) x trivial ((LocallyRingedSpace.Γ.map (a.toLRSHom ≫ π).op).hom r) =
        Point.evaluate ⊤ r (actualChartNativePoint X d p (a.toLRSHom.base x)) :=
    (congrArg (intrinsicEval S (U := ⊤) x trivial)
      (LocallyRingedSpace.Γ_map_comp_apply a.toLRSHom π r)).trans
        ((intrinsicEval_c_app a.toLRSHom a.isCLinear (U := ⊤) x trivial
          ((LocallyRingedSpace.Γ.map π.op).hom r)).trans
            (affineComparisonPoint_eval X d p Z π (actualChartComparison_over X d p)
              (a.toLRSHom.base x) r).symm)
  have hvalues : ∀ (x : S) (r : Γ((actualEtaleNativeScheme X d p).left, ⊤)),
      intrinsicEval S (U := ⊤) x trivial
        ((LocallyRingedSpace.Γ.map (F.toLRSHom ≫ π).op).hom r) =
      intrinsicEval S (U := ⊤) x trivial
        ((LocallyRingedSpace.Γ.map (G.toLRSHom ≫ π).op).hom r) := by
    intro x r
    have hpoint := actualChartReverse_nativePoint X d p x
    have heval :
        Point.evaluate (X := actualEtaleNativeScheme X d p) ⊤ r
          (actualChartNativePoint X d p (F.toLRSHom.base x)) =
        Point.evaluate (X := actualEtaleNativeScheme X d p) ⊤ r
          (actualChartNativePoint X d p (G.toLRSHom.base x)) :=
      congrArg (fun q : ComplexPoint (actualEtaleNativeScheme X d p) =>
        Point.evaluate (X := actualEtaleNativeScheme X d p) ⊤ r q) hpoint
    exact (hv F x r).trans (heval.trans (hv G x r).symm)
  exact @actualEtale_residue_lrs_hom_ext X d
    (inferInstance : SmoothOfRelativeDimension d X.hom) p S.toLocallyRingedSpace
    (F.toLRSHom ≫ π) (G.toLRSHom ≫ π) hcoords (intrinsicStalkEval S)
    (fun x => intrinsicStalkEval_isLocalHom S x) hvalues

/-- The TRUE analytification UP lifts the proved LRS inverse comparison to an AS inverse identity. -/
theorem actualChartReverse_analytic_fac :
    actualChartReverse X d p ≫ affineChartAnalytic X d p =
      (actualChartAnalytification X d p).ofRestrict (actualChartBranch X d p) := by
  apply (analytificationHomEquiv
    ((actualChartAnalytification X d p).restrict (actualChartBranch X d p))
      (actualEtaleSchemeLFT X d p)).injective
  rw [analytificationHomEquiv_apply, analytificationHomEquiv_apply]
  exact Over.OverMorphism.ext (actualChartReverse_comparison X d p)

/-- Actual forward α and actual reverse coordinates are inverse in this order. -/
theorem actualChartForward_reverse :
    actualChartForward X d p ≫ actualChartReverse X d p = 𝟙 (actualEtaleOkaSource X d p) := by
  let I := actualChartOpenInclusion X d p
  letI : Mono I := by dsimp [I, actualChartOpenInclusion]; infer_instance
  apply (cancel_mono I).mp
  change (actualChartForward X d p ≫ actualChartReverse X d p) ≫ actualChartOpenInclusion X d p = _
  rw [Category.assoc, actualChartReverse_fac, ← Category.assoc, actualChartForward_fac,
    affineChartAnalytic_coordinates, Category.id_comp]

/-- Actual reverse coordinates and actual forward α are inverse in the other order. -/
theorem actualChartReverse_forward :
    actualChartReverse X d p ≫ actualChartForward X d p =
      𝟙 ((actualChartAnalytification X d p).restrict (actualChartBranch X d p)) := by
  apply (cancel_mono ((actualChartAnalytification X d p).ofRestrict (actualChartBranch X d p))).mp
  rw [Category.assoc, actualChartForward_fac, actualChartReverse_analytic_fac, Category.id_comp]

/-- The ACTUAL analytic source chart isomorphism required by the native/global gluing bridge. -/
def actualChartIso :
    (actualChartAnalytification X d p).restrict (actualChartBranch X d p) ≅ actualEtaleOkaSource X d p where
  hom := actualChartReverse X d p
  inv := actualChartForward X d p
  hom_inv_id := actualChartReverse_forward X d p
  inv_hom_id := actualChartForward_reverse X d p

end ZInQ.Contrib.CloudB3W17bOkaComparison
