/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Genuine ORIGINAL-data -> ordinary good local-DVR stage join. The original
infinite admissible-order set, K/O/w/hw/A are the ONLY inputs. H4 constructs
the same-closure ordinary field/comap/DVR/Hensel/ind-etale/residue data;
Lane1's certified original-order henselian endpoint constructs N, its
original generic GROUP identification, native abelian-scheme properties
and full source NMP; the already certified ordinary-model join constructs
the good local stage H and actual beta, retaining both GROUP isomorphisms.

No caller N, NMP, generic model iso, presentation, raw stage, properness
supplier, stage geometric connectedness or extra model hypothesis is added.
The original order predicate is not replaced by an extension-base set.
This is the stage producer, NOT effective original-O descent or full NOS:
native M/very-ampleness/line coherence remain separately owned suppliers.

Canonical source world only: FLT/H76 namespace and lane4's frozen canonical
source port are reused, never mixed with the distinct new H5 Lake Source
world. Source producer files, LICENSE/NOTICE and all frozen bytes remain
unchanged. No H4 model/base or Lane1 criterion proof is copied here.
-/
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.HenselianEndpoint
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GoodStageOfOrdinaryModel
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.GenericField
import ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.OrdinaryInside

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ZInQ.Contrib.CloudR2Raynaud.StrictHenselization

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open OrdinaryStages

/-- Construct the actual ordinary model and a true local-DVR good stage
    from ONLY the ORIGINAL target data and ORIGINAL infinite order set.
    Every base/model/presentation/stage property in the conclusion is an
    actual constructed output, not a context premise. -/
theorem exists_good_local_stage_of_original_targetOrders
    {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (hS : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite) :
    ∃ (E : IntermediateField K (AlgebraicClosure K))
      (hE : (w.comap (algebraMap E (AlgebraicClosure K))).comap (algebraMap K E) = O)
      (hDVR : IsDiscreteValuationRing (w.comap (algebraMap E (AlgebraicClosure K)))),
      letI : IsDiscreteValuationRing (w.comap (algebraMap E (AlgebraicClosure K))) := hDVR
      HenselianLocalRing (w.comap (algebraMap E (AlgebraicClosure K))) ∧
      Algebra.IsSeparable K E ∧
      (letI : Algebra O (w.comap (algebraMap E (AlgebraicClosure K))) := (comapHom hE).toAlgebra
       (CommAlgCat.etale.{u} O).ind.{u} (CommAlgCat.of O (w.comap (algebraMap E (AlgebraicClosure K)))) ∧
       ∃ eκ : ResidueField O ≃+* ResidueField (w.comap (algebraMap E (AlgebraicClosure K))),
         residueMap hE = eκ.toRingHom ∧
         (Ordinary.residuePoint eκ).comp (comapHom hE) = residue O ∧
         (∀ σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K),
           σ ∈ w.decompositionSubgroup K → ∀ x ∈ E, σ x = x) ∧
         ∃ N : Grp (Over (Spec (CommRingCat.of (w.comap (algebraMap E (AlgebraicClosure K)))))),
           PkgI2.IsAbelianScheme N ∧
           Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom
             (algebraMap (w.comap (algebraMap E (AlgebraicClosure K))) E)))).mapGrp.obj N ≅
               PkgI2.baseChange A E) ∧
           ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.NeronModelPropertyBundle
             (w.comap (algebraMap E (AlgebraicClosure K))) E N.X.hom ∧
           ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : IsDiscreteValuationRing C)
             (_ : Algebra O C) (H : Grp (Over (Spec (CommRingCat.of C))))
             (β : C →ₐ[O] (w.comap (algebraMap E (AlgebraicClosure K)))),
             Algebra.Etale O C ∧ Module.FaithfullyFlat O C ∧
             IsIso ((stageBase O C).fiberToSpecResidueField (closedPoint O)) ∧
             IsLocalHom β.toRingHom ∧ Function.Injective β ∧
             (letI : Algebra C (w.comap (algebraMap E (AlgebraicClosure K))) := β.toRingHom.toAlgebra
              Module.FaithfullyFlat C (w.comap (algebraMap E (AlgebraicClosure K)))) ∧
             Surjective (Spec.map (CommRingCat.ofHom β.toRingHom)) ∧
             PkgI2.IsAbelianScheme H ∧
             Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom β.toRingHom))).mapGrp.obj H ≅ N) ∧
             Nonempty ((Over.pullback (pullback.fst (stageBase O C) (stageBase O K))).mapGrp.obj H ≅
               (Over.pullback (pullback.snd (stageBase O C) (stageBase O K))).mapGrp.obj A)) := by
  obtain ⟨E, hE, hDVR, hHensel, hSep, hInd, eκ, hκ, hPoint, hFixed⟩ :=
    Ordinary.exists_ordinaryHenselianDVR_inside O w hw
  let P : ValuationSubring E := w.comap (algebraMap E (AlgebraicClosure K))
  letI : IsDiscreteValuationRing P := hDVR
  letI : HenselianLocalRing P := hHensel
  letI : Algebra O P := (comapHom hE).toAlgebra
  obtain ⟨N, hNGood, hGen, hNMP⟩ :=
    ZInQ.Contrib.CloudR2NOS.SingleOrder.PkgBridge.exists_abelianScheme_neronModel_of_targetOrders_henselian
      O w hw A E P hE hS
  letI : PkgI2.IsAbelianScheme N := hNGood
  obtain ⟨genE⟩ := hGen
  obtain ⟨J, hCategory, hFiltered, pres, hEtale⟩ := hInd
  letI : SmallCategory J := hCategory
  letI : IsFiltered J := hFiltered
  have hIndReturn : (CommAlgCat.etale.{u} O).ind.{u} (CommAlgCat.of O P) :=
    ⟨J, hCategory, hFiltered, pres, hEtale⟩
  letI : Algebra O E := ((algebraMap K E).comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O K E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower O P E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hLocal : IsLocalHom (algebraMap O P) :=
    ZInQ.Contrib.CloudR2NOS.Spreadout.isLocalHom_of_comap hE (fun _ => rfl)
  have hInjective : Function.Injective (algebraMap O P) :=
    original_ordinary_comap_injective O E w hE
  have hCartesian := ZInQ.Contrib.CloudR2NOS.Spreadout.isPullback_spec_of_dvr
    (K := K) (E := E) hLocal hInjective
  let Ns : Grp (Over (ZInQ.Contrib.CloudR2NOS.Spreadout.specCone pres).pt) := N
  have genEr : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap P E)))).mapGrp.obj Ns ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K E)))).mapGrp.obj A := genE
  let φP := ZInQ.Contrib.CloudR2NOS.Spreadout.phiOfIsPullback pres K hCartesian Ns A genEr
  have φPr : (Over.pullback (pullback.fst (stageBase O P) (stageBase O K))).mapGrp.obj N ≅
      (Over.pullback (pullback.snd (stageBase O P) (stageBase O K))).mapGrp.obj A := φP
  have hStage := exists_good_stage_from_ordinary_model O E w hE hIndReturn eκ hκ N A φPr
  refine ⟨E, hE, hDVR, ?_⟩
  exact ⟨hHensel, hSep, hIndReturn, eκ, hκ, hPoint, hFixed, N, hNGood, ⟨genE⟩, hNMP, hStage⟩

#print axioms exists_good_local_stage_of_original_targetOrders

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
