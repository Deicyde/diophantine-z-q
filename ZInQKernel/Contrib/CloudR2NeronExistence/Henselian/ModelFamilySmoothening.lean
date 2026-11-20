/-
Copyright 2026 Anthropic, PBC. Apache-2.0; see LICENSE, NOTICE and ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2,
actual constructor solution F1H9 helper (source lines29–120).
NOTICE OF MODIFICATION (2026-11-14): this helper block is moved unchanged in mathematical
content to an earlier module, under its SAME original isolated full namespace.
The final constructor imports it instead of redeclaring it. This isolates the genuinely
ordinary-DVR model-family smoothening step without importing henselian group completion.
No HenselianLocalRing, characteristic, perfectness, or supplied-Néron-model input is added.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT
set_option autoImplicit false


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
h77_open "NeronModelInfra GoodReductionJacobian"
universe u

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing.F1H9

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)}

noncomputable abbrev gfMap {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X) :
    pullback (u ≫ f) (specGenericFibreInclusion R K) ⟶ pullback f (specGenericFibreInclusion R K) :=
  pullback.map (u ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) u
    (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc]
theorem gfMap_snd {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X) :
    gfMap K f u ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd (u ≫ f) (specGenericFibreInclusion R K) := by
  rw [pullback.lift_snd, Category.comp_id]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc]
theorem gfMap_fst {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X) :
    gfMap K f u ≫ pullback.fst f (specGenericFibreInclusion R K) =
      pullback.fst (u ≫ f) (specGenericFibreInclusion R K) ≫ u :=
  pullback.lift_fst _ _ _

theorem exists_smooth_modelFamily [Smooth gK]
    (M₀ : ModelFamily R K gK) (hfin : Finite M₀.ι)
    (hM₀ : ∀ i, IsSeparated (M₀.str i) ∧ LocallyOfFiniteType (M₀.str i) ∧ QuasiCompact (M₀.str i))
    (hpts : M₀.CatchesIndexOnePoints) :
    ∃ M : ModelFamily R K gK, Finite M.ι ∧
      (∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧ QuasiCompact (M.str i)) ∧
      M.CatchesIndexOnePoints := by
  classical
  have hK : ∀ i, Smooth (pullback.snd (M₀.str i) (specGenericFibreInclusion R K)) := fun i => by
    rw [← (M₀.chart i).2]
    infer_instance
  have H : ∀ i, ∃ (X' : Scheme.{u}) (u : X' ⟶ M₀.X i),
      Smooth (u ≫ M₀.str i) ∧ QuasiCompact (u ≫ M₀.str i) ∧ IsSeparated u ∧
      IsIso (gfMap K (M₀.str i) u) ∧
      ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (M₀.str i),
          ∃ x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (u ≫ M₀.str i),
            x'.1 ≫ u = x.1 := fun i => by
    haveI := (hM₀ i).2.1; haveI := (hM₀ i).2.2
    exact NeronModelInfra.exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension K (M₀.str i) (hK i)
  choose X' u hsm hqc hsep hiso hlift using H
  let M : ModelFamily R K gK :=
    { ι := M₀.ι
      X := X'
      str := fun i => u i ≫ M₀.str i
      chart := fun i => NeronModelInfra.schemeHomOverComp ⟨gfMap K (M₀.str i) (u i), gfMap_snd K (M₀.str i) (u i)⟩ (M₀.chart i)
      isOpenImmersion_chart := fun i => by
        haveI := hiso i
        show IsOpenImmersion (gfMap K (M₀.str i) (u i) ≫ (M₀.chart i).1)
        infer_instance }
  refine ⟨M, hfin, fun i => ?_, ?_⟩
  · haveI := hsm i; haveI := hqc i; haveI := hsep i; haveI := (hM₀ i).1
    refine ⟨hsm i, ?_, ?_, hqc i⟩
    · show IsSeparated (u i ≫ M₀.str i); infer_instance
    · show LocallyOfFiniteType (u i ≫ M₀.str i); infer_instance
  · intro R' _ _ _ _ _ K' _ _ _ _ _ _ _ hidx a
    obtain ⟨i, x, hx⟩ := hpts R' K' hidx a
    obtain ⟨x', hx'⟩ := hlift i R' hidx x
    refine ⟨i, x', ?_⟩
    rw [← hx]
    apply Subtype.ext
    show (pointGenericFibre (K := K) (K' := K') x').1 ≫ gfMap K (M₀.str i) (u i) ≫ (M₀.chart i).1 =
      (pointGenericFibre (K := K) (K' := K') x).1 ≫ (M₀.chart i).1
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, gfMap_fst, ← Category.assoc, pointGenericFibre_coe_comp_fst, Category.assoc, hx',
        pointGenericFibre_coe_comp_fst]
    · rw [Category.assoc, gfMap_snd, pointGenericFibre_coe_comp_snd, pointGenericFibre_coe_comp_snd]

end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing.F1H9
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
