/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Join the ACTUAL ordinary pointed presentation, unconditional stage
spreading, and point-selected local-DVR GROUP construction. The raw stage
and its smooth/proper/group/generic identifications are constructed by
Lane3's proved envelope supplier, not caller contexts. Stage abelian-scheme
properties are derived through the actual leg factor and upstairs GROUP
iso. This is a consumer of an ACTUAL upstream model N, not N existence
or a full NOS proof; native M/line suppliers remain separate.
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.Envelope
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.LocalGoodModel
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.OrdinaryComapInput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open OrdinaryStages

/-- Construct a true good local stage from the actual pointed presentation
    and original upstream GROUP model. Neither a raw stage model, a stage
    properness supplier, nor stage geometric connectedness is an input.
    The general base injectivity is supplied by the original comap wrapper
    below, not a new final NOS hypothesis. -/
theorem exists_good_local_stage_of_pointed_presentation
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {P : Type u} [CommRing P] [IsDomain P] [IsLocalRing P] [Algebra O P]
    (hOP : Function.Injective (algebraMap O P))
    (eκ : ResidueField O ≃+* ResidueField P)
    (heκ : ∀ r : O, eκ (residue O r) = residue P (algebraMap O P r))
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (pres : ColimitPresentation J (CommAlgCat.of O P))
    (hEtale : ∀ j : J, Algebra.Etale O (pres.diag.obj j))
    (K : Type u) [Field K] [Algebra O K]
    (N : Grp (Over (Spec (CommRingCat.of P)))) [PkgI2.IsAbelianScheme N]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (φ : (Over.pullback (pullback.fst (stageBase O P) (stageBase O K))).mapGrp.obj N ≅
      (Over.pullback (pullback.snd (stageBase O P) (stageBase O K))).mapGrp.obj A) :
    ∃ (j : Jᵒᵖ) (G : Grp (Over (Spec (CommRingCat.of (pres.diag.obj j.unop)))))
      (s : pres.diag.obj j.unop),
      Smooth G.X.hom ∧ IsProper G.X.hom ∧ IsUnit ((pres.ι.app j.unop).hom s) ∧
      ∃ (_ : IsDomain (Localization.Away s)),
        IsDiscreteValuationRing (Localization.Away s) ∧ Algebra.Etale O (Localization.Away s) ∧
        Module.FaithfullyFlat O (Localization.Away s) ∧
        IsIso ((stageBase O (Localization.Away s)).fiberToSpecResidueField (closedPoint O)) ∧
        ∃ β : Localization.Away s →ₐ[O] P,
          β.comp (IsScalarTower.toAlgHom O (pres.diag.obj j.unop) (Localization.Away s)) =
            (pres.ι.app j.unop).hom ∧
          IsLocalHom β.toRingHom ∧ Function.Injective β ∧
          (letI : Algebra (Localization.Away s) P := β.toRingHom.toAlgebra
           Module.FaithfullyFlat (Localization.Away s) P) ∧
          Surjective (Spec.map (CommRingCat.ofHom β.toRingHom)) ∧
          let H := (Over.pullback (awaySpecMap (pres.diag.obj j.unop) s)).mapGrp.obj G
          PkgI2.IsAbelianScheme H ∧
          Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom β.toRingHom))).mapGrp.obj H ≅ N) ∧
          Nonempty ((Over.pullback (pullback.fst (stageBase O (Localization.Away s)) (stageBase O K))).mapGrp.obj H ≅
            (Over.pullback (pullback.snd (stageBase O (Localization.Away s)) (stageBase O K))).mapGrp.obj A) := by
  haveI : Smooth N.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsProper N.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : Smooth A.X.hom := PkgI2.IsAbelianVariety.smooth
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  let Ns : Grp (Over (ZInQ.Contrib.CloudR2NOS.Spreadout.specCone pres).pt) := N
  haveI : Smooth Ns.X.hom := by
    change Smooth N.X.hom
    infer_instance
  haveI : IsProper Ns.X.hom := by
    change IsProper N.X.hom
    infer_instance
  have hφ : (Over.pullback (ZInQ.Contrib.CloudR2NOS.Spreadout.genFstLim pres K)).mapGrp.obj Ns ≅
      (Over.pullback (ZInQ.Contrib.CloudR2NOS.Spreadout.genSndLim pres K)).mapGrp.obj A := φ
  obtain ⟨j, G, hSm, hPr, iN, iK⟩ :=
    ZInQ.Contrib.CloudR2NOS.Spreadout.exists_spread_stage_envelope pres K Ns A hφ
  letI : Algebra.Etale O (pres.diag.obj j.unop) := hEtale j.unop
  let Graw : Grp (Over (Spec (CommRingCat.of (pres.diag.obj j.unop)))) := G
  haveI : Smooth Graw.X.hom := by
    change Smooth G.X.hom
    exact hSm
  haveI : IsProper Graw.X.hom := by
    change IsProper G.X.hom
    exact hPr
  obtain ⟨iN⟩ := iN
  obtain ⟨iK⟩ := iK
  have iNraw : (Over.pullback (Spec.map (CommRingCat.ofHom (pres.ι.app j.unop).hom.toRingHom))).mapGrp.obj Graw ≅ N := iN
  have iKraw : (Over.pullback (pullback.fst (stageBase O (pres.diag.obj j.unop)) (stageBase O K))).mapGrp.obj Graw ≅
      (Over.pullback (pullback.snd (stageBase O (pres.diag.obj j.unop)) (stageBase O K))).mapGrp.obj A := iK
  have hlocal := exists_local_good_groupStage hOP eκ heκ K (pres.diag.obj j.unop)
    (pres.ι.app j.unop).hom Graw N iNraw A iKraw
  obtain ⟨s, hs, hdom, hdvr, het, hff, hfib, β, hβ, hβloc, hβinj, hffβ, hsurj, hGood, iH, φH⟩ := hlocal
  exact ⟨j, Graw, s, hSm, hPr, hs, hdom, hdvr, het, hff, hfib, β, hβ, hβloc, hβinj,
    hffβ, hsurj, hGood, iH, φH⟩

#print axioms exists_good_local_stage_of_pointed_presentation

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
