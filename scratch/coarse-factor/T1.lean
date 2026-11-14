import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace CoarseFactorAG

variable {K : Type} [Field K] [IsAlgClosed K]

/-- **`K`-points lift along a locally-of-finite-type morphism** through any nonempty closed subset
of the fibre product. -/
theorem exists_lift_of_closed {T S : Scheme.{0}} (t : T ⟶ S) [LocallyOfFiniteType t]
    (a : Spec (CommRingCat.of K) ⟶ S) (F : Set ↥(pullback t a)) (hF : IsClosed F)
    (hne : F.Nonempty) :
    ∃ y : Spec (CommRingCat.of K) ⟶ T, y ≫ t = a ∧
      ∀ u : ↥(Spec (CommRingCat.of K)), y u ∈ (pullback.fst t a) '' F := by
  have : JacobsonSpace ↥(pullback t a) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd t a)
  obtain ⟨q, hqF, hqc⟩ := nonempty_inter_closedPoints hne hF.isLocallyClosed
  have hq : IsClosed ({q} : Set ↥(pullback t a)) := mem_closedPoints_iff.mp hqc
  let s := pointOfClosedPoint (pullback.snd t a) q hq
  refine ⟨s ≫ pullback.fst t a, ?_, fun u => ⟨q, hqF, ?_⟩⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
      Category.id_comp]
  · rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]

/-- `K`-points lift along a surjective locally-of-finite-type morphism. -/
theorem exists_lift_of_surjective {T S : Scheme.{0}} (t : T ⟶ S) [LocallyOfFiniteType t]
    [Surjective t] (a : Spec (CommRingCat.of K) ⟶ S) :
    ∃ y : Spec (CommRingCat.of K) ⟶ T, y ≫ t = a := by
  obtain ⟨q, -⟩ := (pullback.snd t a).surjective
    ((IsLocalRing.closedPoint K : PrimeSpectrum K) : ↥(Spec (CommRingCat.of K)))
  obtain ⟨y, hy, -⟩ := exists_lift_of_closed t a Set.univ isClosed_univ ⟨q, trivial⟩
  exact ⟨y, hy⟩

/-- A `K`-point through a prescribed closed point `y` with `t y = a(pt)`. -/
theorem exists_lift_at {T S : Scheme.{0}} (t : T ⟶ S) [LocallyOfFiniteType t]
    (a : Spec (CommRingCat.of K) ⟶ S) (y : T) (hy : IsClosed ({y} : Set T))
    (u : ↥(Spec (CommRingCat.of K))) (hya : t y = a u) :
    ∃ b : Spec (CommRingCat.of K) ⟶ T, b ≫ t = a ∧ b u = y := by
  obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := a) y u hya
  obtain ⟨b, hb, hb'⟩ := exists_lift_of_closed t a (pullback.fst t a ⁻¹' {y})
    (hy.preimage (pullback.fst t a).continuous) ⟨q, hq⟩
  obtain ⟨q', hq', hq'y⟩ := hb' u
  exact ⟨b, hb, hq'y.symm.trans hq'⟩

end CoarseFactorAG
