import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedBaseChange
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedFiniteSeparable`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Geometric connectedness and finite separable extensions

A scheme over a field is geometrically connected exactly when it remains connected after
base change to every finite separable extension of the field.

## Main results

* `AlgebraicGeometry.geometricallyConnected_iff_forall_finite_separable` characterizes geometric
  connectedness using finite separable field extensions.

## Implementation notes

A scheme over `k` is represented by its structure morphism `f : X ⟶ Spec k`, and its base
change to `k'` is represented by the pullback of `f` along `Spec k' ⟶ Spec k`. Connectedness of
the base change to a separable closure is deduced from connectedness at every finite level: the
comparison morphisms down to the finite levels are integral, universally open and surjective, so
they are closed and open maps, and every quasi-compact open descends to a finite level by
Tag 04KU.

## References

* [Stacks Project, Tag 0389](https://stacks.math.columbia.edu/tag/0389)
-/


open _root_.CategoryTheory
open CategoryTheory Limits

namespace AlgebraicGeometry
#cloudR2LocalInstances

universe u
#cloudR2Vendor connectedSpace_of_finite_level_fibers in

/-- A space mapping onto a family of connected spaces by open and closed maps, such that every
open neighbourhood contains a whole fibre of some member, is connected. -/
private lemma connectedSpace_of_finite_level_fibers {Y : Type*} [TopologicalSpace Y]
    (I : Type*) (Z : I → Type*) [∀ i, TopologicalSpace (Z i)]
    [∀ i, ConnectedSpace (Z i)] (p : ∀ i, Y → Z i)
    (hopen : ∀ i, IsOpenMap (p i)) (hclosed : ∀ i, IsClosedMap (p i))
    (hlocal : ∀ (U : Set Y), IsOpen U → ∀ x ∈ U,
      ∃ i : I, ∀ y, p i y = p i x → y ∈ U)
    [Nonempty Y] : ConnectedSpace Y := by
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, fun U hU ↦ ?_⟩
  by_cases hUempty : U = ∅
  · exact Or.inl hUempty
  right
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hUempty
  obtain ⟨i, hfiber⟩ := hlocal U hU.isOpen x hx
  have himage : IsClopen (p i '' Uᶜ) :=
    ⟨hclosed i Uᶜ hU.compl.isClosed, hopen i Uᶜ hU.compl.isOpen⟩
  rcases isClopen_iff.mp himage with hempty | hfull
  · simpa using Set.image_eq_empty.mp hempty
  · obtain ⟨y, hy, hxy⟩ : p i x ∈ p i '' Uᶜ := hfull.symm ▸ Set.mem_univ _
    exact (hy (hfiber y hxy)).elim
#cloudR2Vendor finiteLevelMap in

/-- The comparison morphism from the base change to a separable closure down to the base change
to a finite intermediate extension. -/
private noncomputable def finiteLevelMap {k K : Type u} [Field k] [Field K]
    [Algebra k K] [IsSepClosure k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : IntermediateField k K) :
    pullback f (spectrumMap k K) ⟶ pullback f (spectrumMap k E) := by
  let y : Spec (.of K) ⟶ Spec (.of E) :=
    Spec.map (CommRingCat.ofHom E.val.toRingHom)
  let gE := spectrumMap k E
  have hy : spectrumMap k K = y ≫ gE := by
    dsimp [spectrumMap, y, gE]
    rw [← Spec.map_comp]
    congr 1
  let e : pullback f (spectrumMap k K) ≅
      pullback (pullback.snd f gE) y :=
    pullback.congrHom rfl hy ≪≫ (pullbackLeftPullbackSndIso f gE y).symm
  exact e.hom ≫ pullback.fst (pullback.snd f gE) y
#cloudR2Vendor finiteLevelMap_isIntegralHom in

/-- The comparison morphism to a finite level is integral. -/
private lemma finiteLevelMap_isIntegralHom {k K : Type u} [Field k] [Field K]
    [Algebra k K] [IsSepClosure k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : IntermediateField k K) :
    IsIntegralHom (finiteLevelMap f E) := by
  unfold finiteLevelMap
  let y : Spec (.of K) ⟶ Spec (.of E) :=
    Spec.map (CommRingCat.ofHom E.val.toRingHom)
  let : IsIntegralHom y := by
    dsimp [y]
    rw [IsIntegralHom.SpecMap_iff]
    exact algebraMap_isIntegral_iff.mpr (Algebra.IsIntegral.tower_top k)
  infer_instance
#cloudR2Vendor finiteLevelMap_universallyOpen in

/-- The comparison morphism to a finite level is universally open. -/
private lemma finiteLevelMap_universallyOpen {k K : Type u} [Field k] [Field K]
    [Algebra k K] [IsSepClosure k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : IntermediateField k K) :
    UniversallyOpen (finiteLevelMap f E) := by
  unfold finiteLevelMap
  infer_instance
#cloudR2Vendor finiteLevelMap_surjective in

/-- The comparison morphism to a finite level is surjective. -/
private lemma finiteLevelMap_surjective {k K : Type u} [Field k] [Field K]
    [Algebra k K] [IsSepClosure k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : IntermediateField k K) :
    Surjective (finiteLevelMap f E) := by
  unfold finiteLevelMap
  infer_instance
#cloudR2Vendor finiteLevelMap_fst in

/-- The comparison morphism to a finite level commutes with the projections to `X`. -/
private lemma finiteLevelMap_fst {k K : Type u} [Field k] [Field K]
    [Algebra k K] [IsSepClosure k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : IntermediateField k K) :
    finiteLevelMap f E ≫ pullback.fst f (spectrumMap k E) =
      pullback.fst f (spectrumMap k K) := by
  unfold finiteLevelMap
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullback.map,
    pullback.lift_fst, CategoryTheory.Category.comp_id]
#cloudR2Vendor finiteLevelMap_snd in

/-- The comparison morphism to a finite level acts on the second projection through the
inclusion of the intermediate field. -/
private lemma finiteLevelMap_snd {k K : Type u} [Field k] [Field K]
    [Algebra k K] [IsSepClosure k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : IntermediateField k K) :
    finiteLevelMap f E ≫ pullback.snd f (spectrumMap k E) =
      pullback.snd f (spectrumMap k K) ≫
        Spec.map (CommRingCat.ofHom E.val.toRingHom) := by
  unfold finiteLevelMap
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst_snd, pullback.congrHom_hom, pullback.map,
    pullback.lift_snd_assoc, CategoryTheory.Category.comp_id]
#cloudR2Vendor connectedSpace_separableClosure in

/-- Connectedness at every finite separable level gives connectedness of the base change to a
separable closure. -/
private lemma connectedSpace_separableClosure {k K : Type u} [Field k] [Field K]
    [Algebra k K] [IsSepClosure k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    (h : ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
      [Algebra.IsSeparable k k'],
      ConnectedSpace ↥(pullback f (spectrumMap k k'))) :
    ConnectedSpace ↥(pullback f (spectrumMap k K)) := by
  let I := {E : IntermediateField k K // FiniteDimensional k E}
  let Z : I → Type u := fun i ↦ ↥(pullback f (spectrumMap k i.1))
  let p : ∀ i : I, ↥(pullback f (spectrumMap k K)) → Z i :=
    fun i ↦ (finiteLevelMap f i.1).base
  have : ∀ i : I, ConnectedSpace (Z i) := by
    intro i
    let : FiniteDimensional k i.1 := i.2
    let : Algebra.IsSeparable k i.1 :=
      Algebra.isSeparable_tower_bot_of_isSeparable k i.1 K
    exact h i.1
  have : Nonempty ↥(pullback f (spectrumMap k K)) := by
    obtain ⟨y⟩ : Nonempty (Z ⟨⊥, inferInstance⟩) := inferInstance
    have := finiteLevelMap_surjective (K := K) f ⊥
    exact ⟨((finiteLevelMap f ⊥).surjective y).choose⟩
  apply connectedSpace_of_finite_level_fibers I Z p
  · exact fun i ↦ have := finiteLevelMap_universallyOpen f i.1; (finiteLevelMap f i.1).isOpenMap
  · exact fun i ↦ have := finiteLevelMap_isIntegralHom f i.1; (finiteLevelMap f i.1).isClosedMap
  · intro U hU x hx
    obtain ⟨W, hWcompact, hWopen, hxW, hWU⟩ :=
      PrespectralSpace.exists_isCompact_and_isOpen_between
        (isCompact_singleton (x := x)) hU (Set.singleton_subset_iff.mpr hx)
    let V : (pullback f (spectrumMap k K)).Opens := ⟨W, hWopen⟩
    obtain ⟨E, hE, V', _, q, hqfst, hqsnd, hV⟩ :=
      exists_finite_subextension_descending_isCompact_open
        X f V hWcompact
    have hq : q = finiteLevelMap f E := by
      apply pullback.hom_ext
      · simpa only [finiteLevelMap_fst] using hqfst
      · simpa only [finiteLevelMap_snd,
          show Spec.map (CommRingCat.ofHom E.val.toRingHom) =
            Spec.map (CommRingCat.ofHom E.val) from rfl] using hqsnd
    refine ⟨⟨E, hE⟩, ?_⟩
    intro y hy
    have hmem : ∀ z : ↥(pullback f (spectrumMap k K)),
        z ∈ W ↔ (finiteLevelMap f E) z ∈ V' := by
      intro z
      have hz := congrArg (fun O : (pullback f (spectrumMap k K)).Opens =>
        z ∈ O) hV
      simpa [V, hq] using hz
    change (finiteLevelMap f E) y = (finiteLevelMap f E) x at hy
    exact hWU ((hmem y).mpr (hy ▸ (hmem x).mp (Set.singleton_subset_iff.mp hxW)))
#cloudR2Vendor geometricallyConnected_iff_forall_finite_separable in

/-- A scheme over a field is geometrically connected if and only if its base change to every
finite separable extension is connected. -/

theorem geometricallyConnected_iff_forall_finite_separable
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    GeometricallyConnected f ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [Algebra.IsSeparable k k'],
        ConnectedSpace ↥(pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))) := by
  refine ⟨fun hf k' _ _ _ _ ↦ hf.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _),
    fun h ↦ ?_⟩
  rw [geometricallyConnected_iff_baseChange_fieldExtension k (SeparableClosure k) f,
    geometricallyConnected_iff_connectedSpace]
  exact connectedSpace_separableClosure f h

end AlgebraicGeometry

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
