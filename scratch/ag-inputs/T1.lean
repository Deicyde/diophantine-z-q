import Mathlib

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

local notation "Qb" => AlgebraicClosure ℚ

example (K : Type) [Field K] : Subsingleton (PrimeSpectrum K) := inferInstance
example (L : Type) [Field L] (f g : ℚ →+* L) : f = g := Subsingleton.elim _ _

theorem spec_rat_ext {L : Type} [Field L] (f g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of ℚ)) :
    f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact Subsingleton.elim _ _

/-- connected over an algebraically closed field ⇒ geometrically connected (leaf form). -/
def ConnectedGeomConnected : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of k)),
    IsProper f → ConnectedSpace Y → GeometricallyConnected f

abbrev Xb (X : Over (Spec (CommRingCat.of ℚ))) : Scheme :=
  pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qb)))

theorem descend_of_leaf (hL : ConnectedGeomConnected) (X : Over (Spec (CommRingCat.of ℚ)))
    (hp : IsProper X.hom) (hc : ConnectedSpace (Xb X)) : GeometricallyConnected X.hom := by
  set q := Spec.map (CommRingCat.ofHom (algebraMap ℚ Qb))
  have hg : GeometricallyConnected (pullback.snd X.hom q) := hL Qb _ _ inferInstance hc
  constructor
  intro K _ y Z fst snd hpb
  let φ : ℚ →+* K := (Spec.preimage y).hom
  have : CharZero K := (RingHom.charZero_iff φ.injective).1 inferInstance
  let L := AlgebraicClosure K
  have : CharZero L := (RingHom.charZero_iff (algebraMap K L).injective).1 inferInstance
  let e : Qb →ₐ[ℚ] L := IsAlgClosed.lift
  let ι : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let se : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of Qb) :=
    Spec.map (CommRingCat.ofHom (e : Qb →+* L))
  have hsq : IsPullback (pullback.fst snd ι ≫ fst) (pullback.snd snd ι) X.hom (ι ≫ y) :=
    (IsPullback.of_hasPullback snd ι).paste_horiz hpb
  have hcomm : se ≫ q = ι ≫ y := spec_rat_ext _ _
  let u : pullback snd ι ⟶ Xb X := pullback.lift (pullback.fst snd ι ≫ fst)
    (pullback.snd snd ι ≫ se) (by rw [hsq.w, Category.assoc, hcomm])
  have hsq' : IsPullback u (pullback.snd snd ι) (pullback.snd X.hom q) se := by
    refine IsPullback.of_right (h₁₂ := pullback.fst X.hom q) (h₂₂ := q) ?_ ?_
      (IsPullback.of_hasPullback X.hom q)
    · rw [pullback.lift_fst, hcomm]; exact hsq
    · rw [pullback.lift_snd]
  let P : Scheme := pullback snd ι
  have : ConnectedSpace P :=
    hg.geometrically_connectedSpace se u (pullback.snd snd ι) hsq'
  have : Surjective ι := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have : Surjective (pullback.fst snd ι) := inferInstance
  exact (Surjective.surj (f := pullback.fst snd ι)).connectedSpace
    (pullback.fst snd ι).continuous
