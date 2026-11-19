import ZInQKernel.Contrib.CloudR2CM.SerreTate.ProperModelStatements
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P4.PropernessFromLocalizations
import ZInQKernel.Contrib.OneProof.NeronExtAb
import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron
import ZInQKernel.Contrib.OneProof.BLRLocalizes
import FrobLift.ResidueFiniteV002

/-!
# A proper global group model from good reduction at every finite place

The unchanged Dedekind Néron input constructs the original global model.
Its localizations are compared with actual proper abelian group models
by the Néron mapping property. The full localization theorem then gives
global properness, with the same generic group identification.
-/

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField

namespace HDec.CMSerreTate.P4

/-- The actual proper smooth abelian group model has the Néron mapping
property for its same generic group identification. -/
theorem groupModelOfAbScheme_isNeron {K : Type} [Field K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (A : _root_.PkgI3.AbVar K)
    (𝒜 : Grp (Over (Spec (CommRingCat.of O)))) [h𝒜 : _root_.PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅
      Grp.mk A.X) : (_root_.ReductGlue.groupModelOfAbScheme O A 𝒜 e).IsNeronModel := by
  haveI : IsProper 𝒜.X.hom := _root_.PkgI2.IsAbelianScheme.proper
  haveI : Smooth 𝒜.X.hom := _root_.PkgI2.IsAbelianScheme.smooth
  have hN := _root_.NeronExt.isNeronModelOver_of_grpObj O K 𝒜.X
  intro Y hY
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))
  let ε : F.obj 𝒜.X ≅ A.X := (Grp.forget _).mapIso e
  have hb : Function.Bijective (fun f : Y ⟶ 𝒜.X => F.map f) := hN.2.2.2.2 Y
  change Function.Bijective (fun f : Y ⟶ 𝒜.X => F.map f ≫ ε.hom)
  have hPost : Function.Bijective (fun g : F.obj Y ⟶ F.obj 𝒜.X => g ≫ ε.hom) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      have hh := congrArg (fun g : F.obj Y ⟶ A.X => g ≫ ε.inv) h
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh
    · intro g
      refine ⟨g ≫ ε.inv, ?_⟩
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hPost.comp hb

/-- Good reduction makes the localization of the same global Néron
model proper, by comparison with the actual good group model. -/
theorem proper_localization_of_good {K : Type} [Field K]
    {A : _root_.PkgI3.AbVar K} {F : Type} [Field F] [NumberField F] [Algebra K F]
    (𝒢 : _root_.ZInQ.DefFaltings.GroupModel A F) (h𝒢 : 𝒢.IsNeronModel)
    (O : ValuationSubring F) [IsDiscreteValuationRing O]
    (hGood : _root_.PkgI2.HasGoodReduction (_root_.ObjBridge.toGrp (A.baseChange F)) O) :
    IsProper (_root_.ReductGlue.toO 𝒢 O).G.hom := by
  obtain ⟨𝒜, h𝒜, ⟨e⟩⟩ := hGood
  letI : _root_.PkgI2.IsAbelianScheme 𝒜 := h𝒜
  let 𝒜model := _root_.ReductGlue.groupModelOfAbScheme O (A.baseChange F) 𝒜 e
  have h𝒜N : 𝒜model.IsNeronModel := groupModelOfAbScheme_isNeron O (A.baseChange F) 𝒜 e
  have hLoc : (_root_.ReductGlue.toO 𝒢 O).IsNeronModel :=
    _root_.GapBLR.neronLocalizesDVR_proved K A F 𝒢 h𝒢 O
  obtain ⟨ε, _⟩ := _root_.ReductGlue.neronO_unique (_root_.ReductGlue.toO 𝒢 O) 𝒜model hLoc h𝒜N
  haveI : IsProper 𝒜model.G.hom := by
    change IsProper 𝒜.X.hom
    exact _root_.PkgI2.IsAbelianScheme.proper
  have hComp : IsProper (ε.hom.left ≫ 𝒜model.G.hom) := inferInstance
  rw [Over.w ε.hom] at hComp
  exact hComp

/-- The exact proper-model obligation, using only the unchanged Dedekind
Néron input and the written good-reduction hypothesis at all finite places. -/
theorem p4ProperModel_proved : HDec.CMSerreTate.P4ProperModel := by
  intro hN L hL hNF E F hF hNFF hAlg hGood
  have hExists := _root_.ZInQ.Contrib.NeronC.neronModelExists_of_extension
    (_root_.ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind hN)
  obtain ⟨𝒢, h𝒢⟩ := hExists L E F
  refine ⟨𝒢, ?_⟩
  apply propernessFromMaximalLocalizations 𝒢
  intro 𝔭 h𝔭
  let O : ValuationSubring F := _root_.ReductGlue.dvrAt 𝔭
  letI : Finite (IsLocalRing.ResidueField O) := _root_.FrobLift.finite_residueField O
  have hAt := hGood O
  change _root_.PkgI2.HasGoodReduction (_root_.ObjBridge.toGrp (E.baseChange F)) O at hAt
  exact proper_localization_of_good 𝒢 h𝒢 O hAt

end HDec.CMSerreTate.P4
