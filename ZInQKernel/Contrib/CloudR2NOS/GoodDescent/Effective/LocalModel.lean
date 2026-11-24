/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

CONSUME the actual Lane3 local étale DVR stage on the SAME stage GROUP.
No raw-stage domain/local/DVR, stage properness Fact, or scheme-only generic
iso is assumed. All local ring/DVR/FF/fibre facts come from LocalStage;
this file only constructs their original model/group/generic-iso application.
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.LocalStage
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GenericRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open OrdinaryStages

/-- Literal refinement morphism Spec(B_s) → Spec B. -/
def awaySpecMap (B : Type u) [CommRing B] (s : B) :
    Spec (CommRingCat.of (Localization.Away s)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))

@[reassoc]
theorem awaySpecMap_base {O B : Type u} [CommRing O] [CommRing B] [Algebra O B] (s : B) :
    awaySpecMap B s ≫ stageBase O B = stageBase O (Localization.Away s) := by
  unfold awaySpecMap stageBase
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The ACTUAL local DVR refinement carries the pullback of the ORIGINAL
    stage group, preserving smoothness/properness and the WHOLE ORIGINAL-K
    generic GROUP identification. -/
theorem exists_local_groupStage
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type u) [Field K] [Algebra O K]
    (B : Type u) [CommRing B] [Algebra O B] [Algebra.Etale O B]
    (aug : B →ₐ[O] IsLocalRing.ResidueField O)
    (G : Grp (Over (Spec (CommRingCat.of B)))) [Smooth G.X.hom] [IsProper G.X.hom]
    (A : Grp (Over (Spec (CommRingCat.of K))))
    (φ : (Over.pullback (pullback.fst (stageBase O B) (stageBase O K))).mapGrp.obj G ≅
      (Over.pullback (pullback.snd (stageBase O B) (stageBase O K))).mapGrp.obj A) :
    ∃ s : B, s ∉ RingHom.ker aug.toRingHom ∧
      ∃ (_ : IsDomain (Localization.Away s)),
        IsDiscreteValuationRing (Localization.Away s) ∧
        Algebra.Etale O (Localization.Away s) ∧
        Module.FaithfullyFlat O (Localization.Away s) ∧
        IsIso ((stageBase O (Localization.Away s)).fiberToSpecResidueField (IsLocalRing.closedPoint O)) ∧
        let H := (Over.pullback (awaySpecMap B s)).mapGrp.obj G
        Smooth H.X.hom ∧ IsProper H.X.hom ∧
        Nonempty ((Over.pullback (pullback.fst (stageBase O (Localization.Away s)) (stageBase O K))).mapGrp.obj H ≅
          (Over.pullback (pullback.snd (stageBase O (Localization.Away s)) (stageBase O K))).mapGrp.obj A) := by
  obtain ⟨s, hs, hloc, ⟨hlocal, hdom, hdvr, hlh, het, hff, huni, hfib⟩, haug, hfactor⟩ :=
    ZInQ.Contrib.CloudR2NOS.Spreadout.LocalStage.exists_localStage B aug
  let H := (Over.pullback (awaySpecMap B s)).mapGrp.obj G
  have hφ := genericPullbackGroupIso_baseChange (stageBase O B)
    (stageBase O (Localization.Away s)) (awaySpecMap B s) (awaySpecMap_base s)
    (stageBase O K) G A φ
  have hSm : Smooth H.X.hom := by
    change Smooth (pullback.snd G.X.hom (awaySpecMap B s))
    exact MorphismProperty.pullback_snd G.X.hom (awaySpecMap B s) (inferInstance : Smooth G.X.hom)
  have hPr : IsProper H.X.hom := by
    change IsProper (pullback.snd G.X.hom (awaySpecMap B s))
    exact MorphismProperty.pullback_snd G.X.hom (awaySpecMap B s) (inferInstance : IsProper G.X.hom)
  exact ⟨s, hs, hdom, hdvr, het, hff, hfib, hSm, hPr, ⟨hφ⟩⟩

/-- The same base-change group model preserves an actual upstairs GROUP
    identification when the original stage leg factors through refinement. -/
def groupModelIso_of_factor
    {U W P : Scheme.{u}} (a : W ⟶ U) (b : P ⟶ W) (c : P ⟶ U) (hc : b ≫ a = c)
    (G : Grp (Over U)) (N : Grp (Over P))
    (i : (Over.pullback c).mapGrp.obj G ≅ N) :
    (Over.pullback b).mapGrp.obj ((Over.pullback a).mapGrp.obj G) ≅ N :=
  pullbackCompGroupIso b a G ≪≫ pullbackCongrGroupIso hc G ≪≫ i

#print axioms exists_local_groupStage
#print axioms groupModelIso_of_factor

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
