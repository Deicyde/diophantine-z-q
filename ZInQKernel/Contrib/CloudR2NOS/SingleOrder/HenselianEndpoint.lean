/-
# H5 / NOS round 2, lane 1: good reduction at a henselian stage inside the original closure,
# from the ORIGINAL infinite order set, with NO model inputs left

Newly authored glue (H5 round-2 lane 1, 2026-11-14), additive to cp4–cp6.
At the original data `K, O, w (w.comap = O), A [IsAbelianVariety]` and a henselian DVR stage
`O' ⊆ E ⊆ AlgebraicClosure K` (`E : IntermediateField K (AlgebraicClosure K)`, `[HenselianLocalRing O']`,
exact comap `O'.comap (algebraMap K E) = O`), the ORIGINAL target set
`{m | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite` gives
`PkgI2.HasGoodReduction (PkgI2.baseChange A E) O'` — the literal target predicate at that stage.

All model data are CONSTRUCTED, none is a hypothesis:
* `PkgI2.IsAbelianVariety (PkgI2.baseChange A E)`: lead's `Extension.isAbelianVariety_baseChange`;
* the model `N`, its generic-fibre group iso `gen`, `IsCommMonObj N.X`, the Néron property `hN` and the
  generic source bundle `hBK`: H4's `NativeLocalNeronModel.exists_group_model` (henselian DVR + fraction
  field + original `PkgI2` abelian variety; built on the published `NeronC.grpObjOfNeron` and H77's
  henselian constructor), applied to `baseChange A E` over `O'`;
* `AbelianSchemePropertyBundle O' N.X.hom`: lane 1's `PkgBridge.abelianSchemePropertyBundle_of_targetOrders_intermediateField`
  (single-order injection + uniform nonproper bound + original-order/scalar join);
* `PkgI2.IsAbelianScheme N` on the SAME `N` (its own group structure untouched): `proper`/`smooth` of
  the bundle and lane 3's `Spreadout.geometricallyConnected_of_bundle`.
This is NOT the original-`O` criterion: the henselian stage `E, O'` is an input (supplied by H4 lane 3's
strict/ordinary henselization-inside constructions); no henselianity of `O` is assumed.
-/
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.PkgBridgeInter
import ZInQKernel.Contrib.CloudR2Raynaud.NativeLocalNeronModel
import ZInQKernel.Contrib.CloudR2NOS.Extension.Abelian
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.SourceModel

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder.PkgBridge

/-- **Good reduction at a henselian stage inside the original closure**, from the ORIGINAL infinite
order set, with every model input constructed. -/
theorem hasGoodReduction_baseChange_of_targetOrders_henselian
    {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (E : IntermediateField K (AlgebraicClosure K))
    (O' : ValuationSubring E) [IsDiscreteValuationRing O'] [HenselianLocalRing O']
    (hE : O'.comap (algebraMap K E) = O)
    (hS : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite) :
    PkgI2.HasGoodReduction (PkgI2.baseChange A E) O' := by
  haveI : PkgI2.IsAbelianVariety (PkgI2.baseChange A E) :=
    ZInQ.Contrib.CloudR2NOS.Extension.isAbelianVariety_baseChange A E
  obtain ⟨N, _, _, _, gen, hcomm, hN, hBK, _⟩ :=
    ZInQ.Contrib.CloudR2Raynaud.NativeLocalNeronModel.exists_group_model (R := O') E
      (PkgI2.baseChange A E)
  haveI := hcomm
  have hASB := abelianSchemePropertyBundle_of_targetOrders_intermediateField O w hw A E O' hE
    N hN hBK gen hS
  exact ⟨N, ⟨hASB.proper, hASB.smooth,
    ZInQ.Contrib.CloudR2NOS.Spreadout.geometricallyConnected_of_bundle hASB⟩, ⟨gen⟩⟩

/-- The same, retaining the constructed model's Néron mapping property (source bundle form)
together with the literal `HasGoodReduction` data. -/
theorem exists_abelianScheme_neronModel_of_targetOrders_henselian
    {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (E : IntermediateField K (AlgebraicClosure K))
    (O' : ValuationSubring E) [IsDiscreteValuationRing O'] [HenselianLocalRing O']
    (hE : O'.comap (algebraMap K E) = O)
    (hS : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite) :
    ∃ N : Grp (Over (Spec (CommRingCat.of O'))), PkgI2.IsAbelianScheme N ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' E)))).mapGrp.obj N ≅
        PkgI2.baseChange A E) ∧
      ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.NeronModelPropertyBundle O' E N.X.hom := by
  haveI : PkgI2.IsAbelianVariety (PkgI2.baseChange A E) :=
    ZInQ.Contrib.CloudR2NOS.Extension.isAbelianVariety_baseChange A E
  obtain ⟨N, _, _, _, gen, hcomm, hN, hBK, _⟩ :=
    ZInQ.Contrib.CloudR2Raynaud.NativeLocalNeronModel.exists_group_model (R := O') E
      (PkgI2.baseChange A E)
  haveI := hcomm
  have hASB := abelianSchemePropertyBundle_of_targetOrders_intermediateField O w hw A E O' hE
    N hN hBK gen hS
  exact ⟨N, ⟨hASB.proper, hASB.smooth,
    ZInQ.Contrib.CloudR2NOS.Spreadout.geometricallyConnected_of_bundle hASB⟩, ⟨gen⟩, hN⟩

end ZInQ.Contrib.CloudR2NOS.SingleOrder.PkgBridge
