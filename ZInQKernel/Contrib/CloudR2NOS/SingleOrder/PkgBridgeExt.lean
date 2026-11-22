/-
# H5 / NOS round 2, lane 1: the original-order / scalar join for a model over an extension

Newly authored glue (H5 round-2 lane 1, 2026-11-14), additive to `PkgBridge.lean` (frozen in cp4).
A supplied model may live over a DVR `R` whose fraction field `E` sits inside the SAME original
closure `Ω = AlgebraicClosure K` (e.g. a henselization/completion-type base produced by H4/H77),
not over the original `O`. This file shows that the ORIGINAL target order set
`{m | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}` (original `K, O, w, A`, same `Ω`,
same orders `m`) feeds the general infinite-orders converse
`PkgBridge.abelianSchemePropertyBundle_of_grp_of_infinite_setOf` for such a model, given:
* a ring map `θ : O →+* R` and the literal triangle
  `∀ o, algebraMap E Ω (algebraMap R E (θ o)) = algebraMap O Ω o` (data of the base, not a
  desired property);
* the model `N : Grp (Over (Spec R))` with commutative law, the (explicit, intermediate) Néron
  property `hN`, the generic-fibre source bundle `hBK`, and a group-object isomorphism
  `e : genericGrp E N ≅ PkgI2.baseChange A E` (generic fibre vs the ORIGINAL `A` base-changed).
The inertia input at every valuation subring of `Ω` containing `R` is derived, with no extra
hypothesis: such a `V` contains `O` through `θ` and the triangle; the lead's
`Extension.inertiaTrivialOn_all_prolongations_baseChange` (fixed `w` → all `V ⊇ O`, incl. `⊤`,
for the SAME `A_E`, `Ω`, `m`) applies; `PkgBridge.inertiaTrivialOn_of_iso` transports along `e`.
Orders: `IsUnit (m : O) → IsUnit (m : R)` via `θ` (`map_natCast`), so the original set is
contained in the `R`-shaped set used by the converse, with the SAME predicate.
`…_valuationSubring` specializes `θ`/triangle to an actual valuation subring `O'` of `E` with
`O'.comap (algebraMap K E) = O`.
No all-prime-powers hypothesis, closure isomorphism, henselianity or perfectness is used.
-/
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.PkgBridge
import ZInQKernel.Contrib.CloudR2NOS.Extension.Torsion

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder.PkgBridge

open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra (specGenericFibreInclusion)

/-- **Original-order / scalar join.** Original `K, O, w (comap = O), A`, the SAME closure
`Ω = AlgebraicClosure K`, an extension `E` (with `IsAlgClosure E Ω`), a DVR `R` with fraction field
`E`, a ring map `θ : O →+* R` with the literal triangle into `Ω`, and a group-object model `N` over
`R` with generic fibre `≅ PkgI2.baseChange A E`: an infinite ORIGINAL target order set makes `N` an
abelian scheme (source bundle). `hN` is an explicit intermediate hypothesis. -/
theorem abelianSchemePropertyBundle_of_targetOrders_extension
    {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (E : Type u) [Field E] [Algebra K E] [Algebra E (AlgebraicClosure K)]
    [IsScalarTower K E (AlgebraicClosure K)] [IsAlgClosure E (AlgebraicClosure K)]
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R E] [IsFractionRing R E]
    (θ : O →+* R)
    (hθ : ∀ o : O, algebraMap E (AlgebraicClosure K) (algebraMap R E (θ o)) =
      algebraMap O (AlgebraicClosure K) o)
    (N : Grp (Over (Spec (CommRingCat.of R)))) [IsCommMonObj N.X]
    (hN : ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.NeronModelPropertyBundle R E N.X.hom)
    (hBK : ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle E
      (pullback.snd N.X.hom (specGenericFibreInclusion R E)))
    (e : genericGrp E N ≅ PkgI2.baseChange A E)
    (hS : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite) :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle R N.X.hom := by
  refine abelianSchemePropertyBundle_of_grp_of_infinite_setOf E N hN hBK (AlgebraicClosure K)
    (fun m => PkgI2.InertiaTrivialOn A w m) ?_ ?_
  · refine Set.Infinite.mono ?_ hS
    rintro m ⟨h0, hu, hq⟩
    refine ⟨h0, ?_, hq⟩
    have h := hu.map θ
    rwa [map_natCast] at h
  · intro m _ _ hq V hV
    refine inertiaTrivialOn_of_iso e V m ?_
    refine ZInQ.Contrib.CloudR2NOS.Extension.inertiaTrivialOn_all_prolongations_baseChange
      (E := E) O w hw A m hq V ?_
    intro o
    have h := hV (θ o)
    rw [hθ o] at h
    -- same `algebraMap O Ω o` up to the (definitionally equal) `Algebra O Ω` instance paths
    exact h

/-- The ring map `O → O'` for a valuation subring `O'` of `E` lying over `O`. -/
def comapRingHom {K : Type u} [Field K] (O : ValuationSubring K) {E : Type u} [Field E]
    [Algebra K E] (O' : ValuationSubring E) (hO' : O'.comap (algebraMap K E) = O) : O →+* O' :=
  ((algebraMap K E).comp O.subtype).codRestrict O'.toSubring (fun o => by
    have ho : (o : K) ∈ O'.comap (algebraMap K E) := hO' ▸ o.2
    exact ho)

/-- **Specialization to an actual valuation subring** `O'` of `E` with the ordinary comap
`O'.comap (algebraMap K E) = O`: `θ` and the triangle are the literal ones. -/
theorem abelianSchemePropertyBundle_of_targetOrders_valuationSubring
    {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (E : Type u) [Field E] [Algebra K E] [Algebra E (AlgebraicClosure K)]
    [IsScalarTower K E (AlgebraicClosure K)] [IsAlgClosure E (AlgebraicClosure K)]
    (O' : ValuationSubring E) [IsDiscreteValuationRing O']
    (hO' : O'.comap (algebraMap K E) = O)
    (N : Grp (Over (Spec (CommRingCat.of O')))) [IsCommMonObj N.X]
    (hN : ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.NeronModelPropertyBundle O' E N.X.hom)
    (hBK : ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle E
      (pullback.snd N.X.hom (specGenericFibreInclusion O' E)))
    (e : genericGrp E N ≅ PkgI2.baseChange A E)
    (hS : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite) :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle O' N.X.hom :=
  abelianSchemePropertyBundle_of_targetOrders_extension O w hw A E O' (comapRingHom O O' hO')
    (fun o => by
      show algebraMap E (AlgebraicClosure K) (algebraMap K E (o : K)) =
        algebraMap O (AlgebraicClosure K) o
      rw [← IsScalarTower.algebraMap_apply K E (AlgebraicClosure K)]
      rfl)
    N hN hBK e hS

end ZInQ.Contrib.CloudR2NOS.SingleOrder.PkgBridge
