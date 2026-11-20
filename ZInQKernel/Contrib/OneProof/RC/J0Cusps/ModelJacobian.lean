import ZInQKernel.Contrib.OneProof.RC.J0Cusps.PointedCurve
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ModelSource
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists

/-! The based Jacobian of the specified normalized curve (tex 1781–1787,
2937–2939). The application of the represented Picard construction is on
the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj PkgI3

namespace ZInQ.Manuscript.RC.J0Cusps

/-- The rational point selected by the width-one formal arc. -/
def infinity (N : ℕ) [NeZero N] : 𝟙_ (Over (Spec (.of ℚ))) ⟶ source N :=
  rationalPoint (X := source N) (X0Model.cusp N) (X0Model.cusp_overQ N)

/-- The chart model as a curve in the represented Picard package. -/
def modelCurve (N : ℕ) [NeZero N] : Curve ℚ :=
  letI : IsIntegral (source N).left := X0Model.integral N
  letI : IsProper (source N).hom := X0Model.proper N
  letI := model_smooth_one N
  pointedSourceCurve (source N) (infinity N)

private theorem modelPicard_exists (N : ℕ) [NeZero N] :
    ∃ (V : AbelianVariety ℚ)
      (rep : (picardFunctorDegree (source N).hom 0).obj.RepresentableBy V.group.X),
      PicardTensorCompatible (source N).hom V.group rep := by
  let X := source N
  letI : X.left.Over (Spec (.of ℚ)) := ⟨X.hom⟩
  letI : IsProper (X.left ↘ Spec (.of ℚ)) := (modelCurve N).isProper
  letI : SmoothOfRelativeDimension 1 X.hom := (modelCurve N).smoothOfRelativeDimension
  letI : SmoothOfRelativeDimension 1 (X.left ↘ Spec (.of ℚ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  letI : GeometricallyIrreducible X.hom := (modelCurve N).geometricallyIrreducible
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  letI : GeometricallyIntegral (X.left ↘ Spec (.of ℚ)) :=
    Smooth.geometricallyIntegral X.hom
  obtain ⟨V, rep, hc, _⟩ := exists_abelianVariety_picardDegreeZero
    (baseField := ℚ) X.left
  exact ⟨V, rep, hc⟩

private def modelPicard (N : ℕ) [NeZero N] : AbelianVariety ℚ :=
  (modelPicard_exists N).choose

/-- The chosen representation of the degree-zero Picard sheaf. -/
def modelPicardRep (N : ℕ) [NeZero N] :
    (picardFunctorDegree (source N).hom 0).obj.RepresentableBy (modelPicard N).group.X :=
  (modelPicard_exists N).choose_spec.choose

/-- The Jacobian of the normalized modular curve. -/
def J0 (N : ℕ) [NeZero N] : AbVar ℚ where
  X := (modelPicard N).group.X
  grp := (modelPicard N).group.grp
  proper := (modelPicard N).proper
  smooth := (modelPicard N).smooth
  geomInt := Smooth.geometricallyIntegral (modelPicard N).group.X.hom

/-- Abel–Jacobi based at the rational width-one cusp of the model. -/
def aj0 (N : ℕ) [NeZero N] : source N ⟶ (J0 N).X :=
  Curve.abelJacobiMap (modelCurve N) (infinity N).left (Over.w (infinity N)) (modelPicardRep N)

/-- Evaluating `aj0` at a point classifies the pullback of the diagonal minus
the constant marked section, i.e. the class of that point minus infinity. -/
theorem aj0_classifies (N : ℕ) [NeZero N] {B : Over (Spec (.of ℚ))} (p : B ⟶ source N) :
    (picardFunctorDegreeι (source N).hom 0).hom.app (.op B)
        ((modelPicardRep N).homEquiv (p ≫ aj0 N)) =
      (toPicardFunctor (source N).hom).app (.op B)
        (Scheme.Pic.map (JacobianChallenge.baseChangeMap (source N).hom p)
          (Curve.abelJacobiClass (modelCurve N) (infinity N).left (Over.w (infinity N)))) :=
  Curve.abelJacobiMap_classifies_pullback (modelCurve N) (infinity N).left
    (Over.w (infinity N)) (modelPicardRep N) p

theorem isJacobian_aj0 (N : ℕ) [NeZero N] :
    LeafModCurves.IsJacobian (source N) (infinity N) (J0 N) (aj0 N) := by
  have alb : IsAlbanese (infinity N) (modelPicard N) (aj0 N) :=
    Curve.isAlbanese_abelJacobiMap (modelCurve N) (infinity N) (modelPicard N) (modelPicardRep N)
      (modelPicard_exists N).choose_spec.choose_spec
  refine ⟨alb.1, ?_⟩
  intro A π hπ
  obtain ⟨g, hg, hg_unique⟩ := alb.existsUnique_schemeMap π hπ
  have : GeometricallyIntegral (modelPicard N).group.X.hom := (J0 N).geomInt
  have hpoint : η[(modelPicard N).group.X] ≫ g = η[A.X] :=
    calc
      _ = (infinity N ≫ aj0 N) ≫ g := congrArg (fun z => z ≫ g) alb.1.symm
      _ = infinity N ≫ (aj0 N ≫ g) := Category.assoc _ _ _
      _ = infinity N ≫ π := congrArg (fun z => infinity N ≫ z) hg.symm
      _ = _ := hπ
  have hmon : IsMonHom g := isMonHom_of_isProper_of_geometricallyIntegral g hpoint
  exact ⟨g, ⟨hmon, hg.symm⟩, fun f hf => hg_unique f hf.2.symm⟩


end ZInQ.Manuscript.RC.J0Cusps
