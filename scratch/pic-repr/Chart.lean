import ZInQKernel.OneProof.H.TailZ24
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Representability

/-! pic-repr §3: `PicRepresentableAbVar` from the vendored open-chart group criterion
(`AlgebraicGeometry.isRepresentable_of_representable_open_subfunctor`, Jacobian-Challenge), for every
abelian variety over every field: everything except the chart is general and proved. The private
vendored lemma `small_picard` (and its helper) is copied verbatim below (Apache-2.0, Jacobian-Challenge
c4254cce, `Jacobian/AlgebraicGeometry/Picard/Representability.lean`, Delaval–Xu–Xu). -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules MonObj

namespace PicRepr

open Scheme

universe u

/-- Verbatim copy of the vendored private helper. -/
lemma hom_ext_of_restrictAdjunction_unit' {scheme : Scheme.{u}}
    {Index : Type*} (cover : Index → scheme.Opens)
    (covers : ∀ point : scheme, ∃ index, point ∈ cover index)
    {sourceModule targetModule : scheme.Modules} {firstMap secondMap : sourceModule ⟶ targetModule}
    (restrictionEquality : ∀ index,
      firstMap ≫ (Modules.restrictAdjunction (cover index).ι).unit.app targetModule =
        secondMap ≫ (Modules.restrictAdjunction (cover index).ι).unit.app targetModule) :
    firstMap = secondMap := by
  refine Modules.hom_ext _ _ fun openSubset ↦ ?_
  ext sectionValue
  let sheaf : TopCat.Sheaf AddCommGrpCat.{u} scheme :=
    ⟨targetModule.presheaf, targetModule.isSheaf⟩
  refine sheaf.eq_of_locally_eq'
    (fun index ↦ (cover index).ι ''ᵁ ((cover index).ι ⁻¹ᵁ openSubset)) openSubset
    (fun index ↦ homOfLE ((cover index).ι.image_preimage_le openSubset))
    (fun point membership ↦ ?_) _ _ fun index ↦ ?_
  · obtain ⟨index, chartMembership⟩ := covers point
    refine Opens.mem_iSup.mpr ⟨index, ?_⟩
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact ⟨chartMembership, membership⟩
  · exact congr(((($(restrictionEquality index)).app openSubset).hom sectionValue))

/-- Verbatim copy of the vendored private `small_picard`: the Picard group of a scheme is small. -/
theorem small_picard' (scheme : Scheme.{u}) : Small.{u} scheme.Pic := by
  classical
  letI := Modules.isGrothendieckAbelian scheme
  let productModule : scheme.Modules := ∏ᶜ fun openSubset : scheme.Opens ↦
    (Modules.pushforward openSubset.ι).obj (SheafOfModules.unit openSubset.toScheme.ringCatSheaf)
  let embedding (moduleSheaf : scheme.Modules) : moduleSheaf ⟶ productModule :=
    Pi.lift fun openSubset ↦
      if trivialization : Nonempty (moduleSheaf.restrict openSubset.ι ≅
          SheafOfModules.unit openSubset.toScheme.ringCatSheaf) then
        (Modules.restrictAdjunction openSubset.ι).unit.app moduleSheaf ≫
          ((Modules.pushforward openSubset.ι).mapIso trivialization.some).hom
      else 0
  have embedding_mono (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] :
      Mono (embedding moduleSheaf) := by
    refine ⟨fun firstMap secondMap equality ↦ hom_ext_of_restrictAdjunction_unit'
      (fun chart : {openSubset : scheme.Opens // Nonempty (moduleSheaf.restrict openSubset.ι ≅
        SheafOfModules.unit openSubset.toScheme.ringCatSheaf)} ↦ chart.1)
      (fun point ↦ ?_) fun chart ↦ ?_⟩
    · obtain ⟨openSubset, membership, ⟨trivialization⟩⟩ :=
        Modules.exists_mem_over_iso_unit moduleSheaf point
      exact ⟨⟨openSubset, ⟨(Modules.restrictFunctorIsoPullback openSubset.ι).app moduleSheaf ≪≫
        Modules.pullbackIotaUnitIsoOfOverIso trivialization⟩⟩, membership⟩
    · have componentEquality := equality =≫ Pi.π _ chart.1
      simp only [Category.assoc, Pi.lift_comp_π, embedding, dif_pos chart.2] at componentEquality
      rw [← Category.assoc, ← Category.assoc] at componentEquality
      exact (cancel_mono _).mp componentEquality
  let classSubobject (lineClass : scheme.Pic) : Subobject productModule :=
    letI := embedding_mono ((fromSkeleton scheme.Modules).obj lineClass.val)
    Subobject.mk (embedding ((fromSkeleton scheme.Modules).obj lineClass.val))
  refine small_of_injective (f := classSubobject) fun firstClass secondClass equality ↦ ?_
  rw [Pic.eq_iff_nonempty_iso]
  letI := embedding_mono ((fromSkeleton scheme.Modules).obj firstClass.val)
  letI := embedding_mono ((fromSkeleton scheme.Modules).obj secondClass.val)
  exact ⟨Subobject.isoOfMkEqMk _ _ equality⟩

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- **The chart hypothesis** (GLUE, not a printed statement) of the vendored group criterion for the
normalized Picard group functor `T ↦ ker(Pic(X_T) → Pic(T))` of `f : X → Spec K` at the section `σ`:
a representable subfunctor `F` that is an open immersion (relative to the forgetful functor), whose
translates by `K`-rational classes contain every field-valued point. These three clauses are copied
from the hypotheses `hFrep`, `hFopen`, `hgen` of `isRepresentable_of_representable_open_subfunctor`. -/
def PicChart (f : X ⟶ Spec (.of K)) (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ f = 𝟙 _) : Prop :=
  ∃ F : Subfunctor (picardFunctorNormalizedGrp f σ hσ ⋙ forget GrpCat.{1}),
    F.toFunctor.IsRepresentable ∧
    (IsOpenImmersion.inverseImage (Over.forget (Spec (.of K)))).relative uliftYoneda.{1} F.ι ∧
    ∀ (L : Type) [Field L] [Algebra K L]
      (g : (picardFunctorNormalizedGrp f σ hσ).obj
        (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))),
      ∃ g' : (picardFunctorNormalizedGrp f σ hσ).obj (.op (Over.mk (𝟙 (Spec (.of K))))),
        ((picardFunctorNormalizedGrp f σ hσ).map (Over.homMk (Spec.map (CommRingCat.ofHom
            (algebraMap K L))) (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
              Over.mk (𝟙 (Spec (.of K)))).op).hom g' * g ∈
          F.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))

/-- **Reduction (compiled).** For `X` proper and geometrically integral over a field `K` with a
rational point, a chart of the normalized Picard group functor gives a representation of the
relative Picard fppf sheaf. Proved from the vendored criterion, the Zariski sheaf property of
normalized classes, smallness, and the normalization isomorphism at a rational point (Kleiman 9.2.5
in the vendored form). -/
theorem representable_of_picChart (f : X ⟶ Spec (.of K)) [IsProper f] [GeometricallyIntegral f]
    (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (hc : PicChart f σ hσ) :
    ∃ P : Over (Spec (.of K)), Nonempty ((picardFunctor f).obj.RepresentableBy P) := by
  letI : X.Over (Spec (.of K)) := ⟨f⟩
  letI : IsProper (X ↘ Spec (.of K)) := inferInstanceAs (IsProper f)
  letI : GeometricallyIntegral (X ↘ Spec (.of K)) := inferInstanceAs (GeometricallyIntegral f)
  obtain ⟨F, hFrep, hFopen, hgen⟩ := hc
  have smallValues (T : (Over (Spec (.of K)))ᵒᵖ) :
      Small.{0} ((picardFunctorNormalizedGrp f σ hσ ⋙ forget GrpCat.{1}).obj T) := by
    letI := small_picard' (pullback f T.unop.hom)
    exact small_subtype _ _
  obtain ⟨P, _, ⟨rep⟩⟩ :=
    isRepresentable_of_representable_open_subfunctor (picardFunctorNormalizedGrp f σ hσ) F
      smallValues
      (isSheaf_zariski_picardFunctorNormalized f σ hσ
        isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral)
      hFrep hFopen hgen
  exact ⟨P, ⟨rep.ofIso (normalizedPicardIso (source := X) σ hσ)⟩⟩

/-- **Converse (compiled): the chart hypothesis is not strictly smaller.** If the Picard sheaf is
representable, the whole functor `⊤` is a chart. So `PicChart` is equivalent to representability; a
genuine reduction must name a concrete chart (for curves: the cohomology chart into the Hilbert scheme
of points). -/
theorem picChart_of_representable (f : X ⟶ Spec (.of K)) [IsProper f] [GeometricallyIntegral f]
    (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (h : ∃ P : Over (Spec (.of K)), Nonempty ((picardFunctor f).obj.RepresentableBy P)) :
    PicChart f σ hσ := by
  letI : X.Over (Spec (.of K)) := ⟨f⟩
  letI : IsProper (X ↘ Spec (.of K)) := inferInstanceAs (IsProper f)
  letI : GeometricallyIntegral (X ↘ Spec (.of K)) := inferInstanceAs (GeometricallyIntegral f)
  obtain ⟨P, ⟨rep⟩⟩ := h
  refine ⟨⊤, ?_, ?_, ?_⟩
  · exact (rep.ofIso ((asIso (⊤ : Subfunctor (picardFunctorNormalizedGrp f σ hσ ⋙
      forget GrpCat.{1})).ι) ≪≫ normalizedPicardIso (source := X) σ hσ).symm).isRepresentable
  · exact relative_isOpenImmersion_of_exists_opens fun T x => ⟨⊤, fun W a => by simp⟩
  · intro L _ _ g
    exact ⟨1, Set.mem_univ _⟩

theorem picChart_iff (f : X ⟶ Spec (.of K)) [IsProper f] [GeometricallyIntegral f]
    (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ f = 𝟙 _) :
    PicChart f σ hσ ↔
      ∃ P : Over (Spec (.of K)), Nonempty ((picardFunctor f).obj.RepresentableBy P) :=
  ⟨representable_of_picChart f σ hσ, picChart_of_representable f σ hσ⟩

/-- The zero section of an abelian variety is a section of its structure morphism. -/
theorem zero_section (A : PkgI3.AbVar K) :
    (η[A.X].left : Spec (.of K) ⟶ A.X.left) ≫ A.X.hom = 𝟙 _ := by
  simp

/-- **The chart Prop for abelian varieties** (GLUE; equivalent to the field by `picChart_iff`):
a chart of the normalized Picard group functor at the zero section. -/
def PicChartAbVar : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K), PicChart A.X.hom (η[A.X].left) (zero_section A)

/-- The field from the chart Prop (compiled). -/
theorem picRepresentableAbVar_of_chart (h : PicChartAbVar) : T09Pic.PicRepresentableAbVar :=
  fun K _ A => representable_of_picChart A.X.hom _ _ (h K A)

/-- And back: the chart Prop from the field (compiled). -/
theorem picChartAbVar_of_field (h : T09Pic.PicRepresentableAbVar) : PicChartAbVar :=
  fun K _ A => picChart_of_representable A.X.hom _ _ (h K A)

end PicRepr

#print axioms PicRepr.picRepresentableAbVar_of_chart
#print axioms PicRepr.picChartAbVar_of_field
