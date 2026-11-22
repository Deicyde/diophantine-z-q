/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Construct a TRUE local-DVR abelian stage directly from an actual ordinary
same-closure model and its original generic GROUP identification. The raw
presentation, stage model, properness, point refinement, beta properties
and stage geometric connectedness are all produced by the proved suppliers.
No stage model/properness/GC/injective leg or arbitrary ramified extension
is a caller premise. Upstream N itself is an explicit model input here;
its existence and the native M/line extension are not claimed by this join.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.OrdinaryModelStageJoin
import ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.OrdinaryPresentation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ZInQ.Contrib.CloudR2Raynaud.StrictHenselization

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open OrdinaryStages

/-- The actual same-closure ind-étale and original-residue supplier plus
    the actual upstairs good GROUP model produce a good local DVR stage.
    The original A/K/O and all actual base maps remain unchanged. -/
theorem exists_good_stage_from_ordinary_model
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (E : IntermediateField K Ω) (w : ValuationSubring Ω)
    (hE : (w.comap (algebraMap E Ω)).comap (algebraMap K E) = O) :
    letI : Algebra O (w.comap (algebraMap E Ω)) := (comapHom hE).toAlgebra
    ∀ (hind : (CommAlgCat.etale.{u} O).ind.{u} (CommAlgCat.of O (w.comap (algebraMap E Ω))))
      (eκ : ResidueField O ≃+* ResidueField (w.comap (algebraMap E Ω)))
      (hκ : residueMap hE = eκ.toRingHom)
      (N : Grp (Over (Spec (CommRingCat.of (w.comap (algebraMap E Ω))))))
      [PkgI2.IsAbelianScheme N]
      (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
      (φ : (Over.pullback (pullback.fst (stageBase O (w.comap (algebraMap E Ω))) (stageBase O K))).mapGrp.obj N ≅
        (Over.pullback (pullback.snd (stageBase O (w.comap (algebraMap E Ω))) (stageBase O K))).mapGrp.obj A),
      ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : IsDiscreteValuationRing C)
        (_ : Algebra O C) (H : Grp (Over (Spec (CommRingCat.of C))))
        (β : C →ₐ[O] (w.comap (algebraMap E Ω))),
        Algebra.Etale O C ∧ Module.FaithfullyFlat O C ∧
        IsIso ((stageBase O C).fiberToSpecResidueField (closedPoint O)) ∧
        IsLocalHom β.toRingHom ∧ Function.Injective β ∧
        (letI : Algebra C (w.comap (algebraMap E Ω)) := β.toRingHom.toAlgebra
         Module.FaithfullyFlat C (w.comap (algebraMap E Ω))) ∧
        Surjective (Spec.map (CommRingCat.ofHom β.toRingHom)) ∧
        PkgI2.IsAbelianScheme H ∧
        Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom β.toRingHom))).mapGrp.obj H ≅ N) ∧
        Nonempty ((Over.pullback (pullback.fst (stageBase O C) (stageBase O K))).mapGrp.obj H ≅
          (Over.pullback (pullback.snd (stageBase O C) (stageBase O K))).mapGrp.obj A) := by
  letI : Algebra O (w.comap (algebraMap E Ω)) := (comapHom hE).toAlgebra
  intro hind eκ hκ N _ A _ φ
  have heκ : ∀ r : O, eκ (residue O r) =
      residue (w.comap (algebraMap E Ω)) (algebraMap O (w.comap (algebraMap E Ω)) r) := by
    intro r
    have h := residueMap_residue hE r
    rw [hκ] at h
    exact h
  obtain ⟨J, hcat, hfilt, pres, het⟩ := hind
  letI : SmallCategory J := hcat
  letI : IsFiltered J := hfilt
  obtain ⟨j, G, s, hSm, hPr, hs, hdom, hdvr, hetC, hffC, hfib,
      β, hβ, hβloc, hβinj, hffβ, hsurj, hGood, iH, φH⟩ :=
    exists_good_local_stage_of_pointed_presentation (original_ordinary_comap_injective O E w hE)
      eκ heκ pres het K N A φ
  let C : Type u := Localization.Away s
  letI : IsDomain C := hdom
  letI : IsDiscreteValuationRing C := hdvr
  let H := (Over.pullback (awaySpecMap (pres.diag.obj j.unop) s)).mapGrp.obj G
  exact ⟨C, inferInstance, hdom, hdvr, inferInstance, H, β, hetC, hffC, hfib,
    hβloc, hβinj, hffβ, hsurj, hGood, iH, φH⟩

#print axioms exists_good_stage_from_ordinary_model

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
