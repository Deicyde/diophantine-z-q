/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

ACTUAL LocalStage factor β → Spec surjectivity → stage abelian scheme.
The general DVR-map faithful-flatness theorem is consumed from Lane3;
β's locality and injectivity are DERIVED in BetaFactory. Geometric
connectedness is reflected through the SAME upstairs GROUP iso. No
hStageGC, raw-stage domain/DVR, or ind-étaleness B_s → P is assumed.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.BetaFactory
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.StageGoodTransport
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.LocalFaithfullyFlat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open OrdinaryStages

/-- The ORIGINAL stage-leg factor gives the literal Spec composite. -/
@[reassoc]
theorem factor_spec_comp {O B P : Type u} [CommRing O] [CommRing B] [CommRing P]
    [Algebra O B] [Algebra O P] (s : B) (ι : B →ₐ[O] P)
    (β : Localization.Away s →ₐ[O] P)
    (hβ : β.comp (IsScalarTower.toAlgHom O B (Localization.Away s)) = ι) :
    Spec.map (CommRingCat.ofHom β.toRingHom) ≫ awaySpecMap B s =
      Spec.map (CommRingCat.ofHom ι.toRingHom) := by
  unfold awaySpecMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f : B →+* P => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom hβ)

/-- Construct the SAME point-refined stage GROUP as an actual abelian
    scheme. The needed geometric connectedness follows from the ACTUAL
    β and original upstairs GROUP iso; it is NOT an input to this theorem.
    O → P injectivity comes from the original same-closure comap, not the
    possibly noninjective raw stage leg. -/
theorem exists_local_good_groupStage
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {P : Type u} [CommRing P] [IsDomain P] [IsLocalRing P] [Algebra O P]
    (hOP : Function.Injective (algebraMap O P))
    (e : ResidueField O ≃+* ResidueField P)
    (he : ∀ r : O, e (residue O r) = residue P (algebraMap O P r))
    (K : Type u) [Field K] [Algebra O K]
    (B : Type u) [CommRing B] [Algebra O B] [Algebra.Etale O B] (ι : B →ₐ[O] P)
    (G : Grp (Over (Spec (CommRingCat.of B)))) [Smooth G.X.hom] [IsProper G.X.hom]
    (N : Grp (Over (Spec (CommRingCat.of P)))) [PkgI2.IsAbelianScheme N]
    (iN : (Over.pullback (Spec.map (CommRingCat.ofHom ι.toRingHom))).mapGrp.obj G ≅ N)
    (A : Grp (Over (Spec (CommRingCat.of K))))
    (φ : (Over.pullback (pullback.fst (stageBase O B) (stageBase O K))).mapGrp.obj G ≅
      (Over.pullback (pullback.snd (stageBase O B) (stageBase O K))).mapGrp.obj A) :
    ∃ s : B, IsUnit (ι s) ∧
      ∃ (_ : IsDomain (Localization.Away s)),
        IsDiscreteValuationRing (Localization.Away s) ∧ Algebra.Etale O (Localization.Away s) ∧
        Module.FaithfullyFlat O (Localization.Away s) ∧
        IsIso ((stageBase O (Localization.Away s)).fiberToSpecResidueField (closedPoint O)) ∧
        ∃ β : Localization.Away s →ₐ[O] P,
          β.comp (IsScalarTower.toAlgHom O B (Localization.Away s)) = ι ∧
          IsLocalHom β.toRingHom ∧ Function.Injective β ∧
          (letI : Algebra (Localization.Away s) P := β.toRingHom.toAlgebra
           Module.FaithfullyFlat (Localization.Away s) P) ∧
          Surjective (Spec.map (CommRingCat.ofHom β.toRingHom)) ∧
          let H := (Over.pullback (awaySpecMap B s)).mapGrp.obj G
          PkgI2.IsAbelianScheme H ∧
          Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom β.toRingHom))).mapGrp.obj H ≅ N) ∧
          Nonempty ((Over.pullback (pullback.fst (stageBase O (Localization.Away s)) (stageBase O K))).mapGrp.obj H ≅
            (Over.pullback (pullback.snd (stageBase O (Localization.Away s)) (stageBase O K))).mapGrp.obj A) := by
  obtain ⟨s, hs, hloc, hlocal, hdom, hdvr, het, hffO, hfib, β, hβ, hβlocal, hβinj⟩ :=
    exists_localStage_factor_properties hOP e he B ι
  letI : IsLocalRing (Localization.Away s) := hlocal
  letI : IsDomain (Localization.Away s) := hdom
  letI : IsDiscreteValuationRing (Localization.Away s) := hdvr
  letI : IsLocalHom β.toRingHom := hβlocal
  have hffβ : (letI : Algebra (Localization.Away s) P := β.toRingHom.toAlgebra
      Module.FaithfullyFlat (Localization.Away s) P) :=
    ZInQ.Contrib.CloudR2NOS.Spreadout.LocalFaithfullyFlat.faithfullyFlat_of_ringHom β.toRingHom hβinj
  let pβ : Spec (CommRingCat.of P) ⟶ Spec (CommRingCat.of (Localization.Away s)) :=
    Spec.map (CommRingCat.ofHom β.toRingHom)
  haveI : Surjective pβ :=
    ZInQ.Contrib.CloudR2NOS.Spreadout.LocalFaithfullyFlat.surjective_specMap_of_ringHom β.toRingHom hβinj
  let H := (Over.pullback (awaySpecMap B s)).mapGrp.obj G
  let iH : (Over.pullback pβ).mapGrp.obj H ≅ N :=
    groupModelIso_of_factor (awaySpecMap B s) pβ (Spec.map (CommRingCat.ofHom ι.toRingHom))
      (factor_spec_comp s ι β hβ) G N iN
  haveI : Smooth H.X.hom := by
    change Smooth (pullback.snd G.X.hom (awaySpecMap B s))
    exact MorphismProperty.pullback_snd G.X.hom (awaySpecMap B s) (inferInstance : Smooth G.X.hom)
  haveI : IsProper H.X.hom := by
    change IsProper (pullback.snd G.X.hom (awaySpecMap B s))
    exact MorphismProperty.pullback_snd G.X.hom (awaySpecMap B s) (inferInstance : IsProper G.X.hom)
  have hGood : PkgI2.IsAbelianScheme H := isAbelianScheme_of_surjective_groupIso pβ H N iH
  have iK := genericPullbackGroupIso_baseChange (stageBase O B) (stageBase O (Localization.Away s))
    (awaySpecMap B s) (awaySpecMap_base s) (stageBase O K) G A φ
  exact ⟨s, hs, hdom, hdvr, het, hffO, hfib, β, hβ, hβlocal, hβinj, hffβ, inferInstance,
    hGood, ⟨iH⟩, ⟨iK⟩⟩

#print axioms exists_local_good_groupStage

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
