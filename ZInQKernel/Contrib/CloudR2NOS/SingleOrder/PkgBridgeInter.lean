/-
# H5 / NOS round 2, lane 1: consumer adapter for an extension base given as an intermediate field

Newly authored glue (H5 round-2 lane 1, 2026-11-14), additive to `PkgBridgeExt.lean` (frozen in cp5).
H4 lane 3's certified strict / ordinary henselization-inside constructions
(`StrictHenselization.exists_strictlyHenselianDVR_inside`,
`StrictHenselization.Ordinary.exists_ordinaryHenselianDVR_inside`, reported by that lane; not imported
or copied here) output `E : IntermediateField K (AlgebraicClosure K)` and a DVR `O' : ValuationSubring E`
with the EXACT comap `O'.comap (algebraMap K E) = O` (and `O' = w.comap (algebraMap E Ω)`). This adapter
consumes exactly that shape: the instance `IsAlgClosure E (AlgebraicClosure K)` is installed from the
lead's `Extension.isAlgClosure_over_intermediateField` (same Ω, tower-top algebraicity; no perfectness),
then `PkgBridge.abelianSchemePropertyBundle_of_targetOrders_valuationSubring` applies.
`hN` remains an explicit intermediate hypothesis; nothing here supplies a model.
-/
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.PkgBridgeExt
import ZInQKernel.Contrib.CloudR2NOS.Extension.Closure

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder.PkgBridge

open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra (specGenericFibreInclusion)

/-- **Adapter for an intermediate-field base inside the SAME original closure.** -/
theorem abelianSchemePropertyBundle_of_targetOrders_intermediateField
    {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (E : IntermediateField K (AlgebraicClosure K))
    (O' : ValuationSubring E) [IsDiscreteValuationRing O']
    (hE : O'.comap (algebraMap K E) = O)
    (N : Grp (Over (Spec (CommRingCat.of O')))) [IsCommMonObj N.X]
    (hN : ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.NeronModelPropertyBundle O' E N.X.hom)
    (hBK : ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle E
      (pullback.snd N.X.hom (specGenericFibreInclusion O' E)))
    (e : genericGrp E N ≅ PkgI2.baseChange A E)
    (hS : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite) :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle O' N.X.hom := by
  haveI : IsAlgClosure E (AlgebraicClosure K) :=
    ZInQ.Contrib.CloudR2NOS.Extension.isAlgClosure_over_intermediateField K E
  exact abelianSchemePropertyBundle_of_targetOrders_valuationSubring O w hw A E O' hE N hN hBK e hS

/-- The ring map used by the specialization is literally the ORIGINAL `PkgI2.toW`. -/
theorem comapRingHom_eq_toW {K : Type u} [Field K] (O : ValuationSubring K) {E : Type u} [Field E]
    [Algebra K E] (O' : ValuationSubring E) (hO' : O'.comap (algebraMap K E) = O) :
    comapRingHom O O' hO' = PkgI2.toW O O' hO' :=
  rfl

end ZInQ.Contrib.CloudR2NOS.SingleOrder.PkgBridge
