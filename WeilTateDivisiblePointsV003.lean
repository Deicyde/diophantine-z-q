import ZInQKernel.Contrib.CloudB3W16Torsion.NativeBridges
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Divisibility of the actual point group over an algebraically closed field, with no degree formula

For `A : PkgI3.AbVar K`, `n` with `(n : K) ≠ 0`, and any algebraically closed field `Ω` over `K`:

* `mulN_surjective`: the morphism of schemes underlying `[n] = 𝟙 ^ n` is surjective.  It is étale
  (`CloudB3W16Torsion.multiplication_etale`), hence flat and locally of finite presentation, hence open; it is
  finite (`CloudB3W16Torsion.multiplication_finite`), hence proper, hence closed; its image is nonempty and
  `A` is irreducible (geometrically integral over a field), so the image is everything;
* `exists_section_of_surjective`: a surjective locally finite type scheme over `Spec Ω` has an `Ω`-point
  (closed points of a Jacobson scheme have residue field `Ω`; the same argument as the rational point lifts of
  the semistable-geometry lane);
* `pt_pow_surjective`: every `x : A.Pt Ω` (the repository's `Ω`-points, `K`-morphisms `Spec Ω → A`) is an
  `n`-th power `y ^ n` with `y : A.Pt Ω`.

No cardinality, degree, rank or basis of the torsion is used.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace WeilTate.Divisible

/-- A surjective locally finite type scheme over an algebraically closed field has a rational point. -/
theorem exists_section_of_surjective {Ω : Type} [Field Ω] [IsAlgClosed Ω] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of Ω)) [LocallyOfFiniteType f] (hf : Function.Surjective f) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ X, p ≫ f = 𝟙 _ := by
  haveI : Nonempty X := ⟨(hf (IsLocalRing.closedPoint Ω)).choose⟩
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, _, hxc⟩ := nonempty_inter_closedPoints (Set.univ_nonempty : (Set.univ : Set X).Nonempty)
    isOpen_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint f x hxc, pointOfClosedPoint_comp f x hxc⟩

variable {K : Type} [Field K] (A : PkgI3.AbVar K)

/-- **`[n]` is surjective on the underlying scheme** for `n` invertible in `K`. -/
theorem mulN_surjective (n : ℕ) (hnK : (n : K) ≠ 0) :
    Function.Surjective ((𝟙 A.X ^ n : A.X ⟶ A.X).left) := by
  haveI he : Etale ((𝟙 A.X ^ n : A.X ⟶ A.X).left) :=
    ZInQ.Contrib.CloudB3W16Torsion.multiplication_etale (ObjBridge.toGrp A) n hnK
  haveI hfin : IsFinite ((𝟙 A.X ^ n : A.X ⟶ A.X).left) :=
    ZInQ.Contrib.CloudB3W16Torsion.multiplication_finite (ObjBridge.toGrp A) n hnK
  haveI : Smooth ((𝟙 A.X ^ n : A.X ⟶ A.X).left) := inferInstance
  haveI : Flat ((𝟙 A.X ^ n : A.X ⟶ A.X).left) := inferInstance
  haveI : LocallyOfFinitePresentation ((𝟙 A.X ^ n : A.X ⟶ A.X).left) := inferInstance
  haveI : UniversallyOpen ((𝟙 A.X ^ n : A.X ⟶ A.X).left) := UniversallyOpen.of_flat _
  haveI : IsProper ((𝟙 A.X ^ n : A.X ⟶ A.X).left) := inferInstance
  have hopen := ((𝟙 A.X ^ n : A.X ⟶ A.X).left).isOpenMap.isOpen_range
  have hclosed := ((𝟙 A.X ^ n : A.X ⟶ A.X).left).isClosedMap.isClosed_range
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  haveI : PreconnectedSpace A.X.left :=
    ⟨(IsIrreducible.isConnected (IrreducibleSpace.isIrreducible_univ A.X.left)).isPreconnected⟩
  haveI : Nonempty A.X.left := ⟨η[A.X].left (IsLocalRing.closedPoint K)⟩
  rcases isClopen_iff.mp ⟨hclosed, hopen⟩ with h | h
  · exfalso
    have hne : (Set.range ((𝟙 A.X ^ n : A.X ⟶ A.X).left)).Nonempty :=
      Set.range_nonempty _
    rw [h] at hne
    exact Set.not_nonempty_empty hne
  · exact Set.range_eq_univ.mp h

/-- **Every `Ω`-point of `A` is an `n`-th power**, for `Ω` algebraically closed over `K` and `n` invertible
in `K`. -/
theorem pt_pow_surjective {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (n : ℕ)
    (hnK : (n : K) ≠ 0) (x : A.Pt Ω) : ∃ y : A.Pt Ω, y ^ n = x := by
  set m : A.X ⟶ A.X := 𝟙 A.X ^ n with hm
  haveI hfin : IsFinite m.left :=
    ZInQ.Contrib.CloudB3W16Torsion.multiplication_finite (ObjBridge.toGrp A) n hnK
  have hsurj : Function.Surjective m.left := mulN_surjective A n hnK
  haveI : Surjective m.left := ⟨hsurj⟩
  haveI : LocallyOfFiniteType m.left := inferInstance
  haveI hS : Surjective (pullback.snd m.left x.left) := inferInstance
  haveI : LocallyOfFiniteType (pullback.snd m.left x.left) := inferInstance
  obtain ⟨p, hp⟩ := exists_section_of_surjective (Ω := Ω) (pullback.snd m.left x.left) hS.surj
  let f : pullback m.left x.left ⟶ Spec (CommRingCat.of Ω) := pullback.snd m.left x.left
  have hmw : m.left ≫ A.X.hom = A.X.hom := Over.w m
  let y : A.Pt Ω := Over.homMk (p ≫ pullback.fst m.left x.left) (by
    change (p ≫ pullback.fst m.left x.left) ≫ A.X.hom = (PkgI3.AbVar.ptObj (K := K) Ω).hom
    rw [← hmw, Category.assoc, ← Category.assoc (pullback.fst m.left x.left), pullback.condition,
      Category.assoc, Over.w x, ← Category.assoc]
    change (p ≫ f) ≫ _ = _
    rw [hp]
    exact Category.id_comp _)
  refine ⟨y, ?_⟩
  have hpow : y ^ n = y ≫ m := by
    rw [hm, MonObj.comp_pow, Category.comp_id]
  rw [hpow]
  apply Over.OverMorphism.ext
  change (p ≫ pullback.fst m.left x.left) ≫ m.left = x.left
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  change (p ≫ f) ≫ x.left = x.left
  rw [hp]
  exact Category.id_comp _

end WeilTate.Divisible

#check @WeilTate.Divisible.exists_section_of_surjective
#check @WeilTate.Divisible.mulN_surjective
#check @WeilTate.Divisible.pt_pow_surjective
#print axioms WeilTate.Divisible.exists_section_of_surjective
#print axioms WeilTate.Divisible.mulN_surjective
#print axioms WeilTate.Divisible.pt_pow_surjective
