import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.ZMod.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! The prime-power torsion subschemes jointly detect regular functions
on a split torus over any ring. -/

noncomputable section

set_option linter.style.haveILetI false

namespace SZRaynaud

/-- Reduction of the exponent lattice of the split torus. -/
def modToricExponent (r m : ℕ) : (Fin r → ℤ) →+ (Fin r → ZMod m) where
  toFun a i := (a i : ZMod m)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

/-- Reduction modulo sufficiently large powers of ℓ separates any prescribed
finite set of Laurent exponents. -/
theorem exists_injOn_modToricExponent {r ℓ : ℕ} (hℓ : 1 < ℓ)
    (s : Finset (Fin r → ℤ)) :
    ∃ n : ℕ, Set.InjOn (modToricExponent r (ℓ ^ n)) (s : Set (Fin r → ℤ)) := by
  classical
  let N := s.sup (fun a => (Finset.univ : Finset (Fin r)).sup (fun i => (a i).natAbs))
  have hN (a : Fin r → ℤ) (ha : a ∈ s) (i : Fin r) : (a i).natAbs ≤ N := by
    have hi : (a i).natAbs ≤ (Finset.univ : Finset (Fin r)).sup (fun j => (a j).natAbs) :=
      Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)
    exact hi.trans (Finset.le_sup (f := fun a => (Finset.univ : Finset (Fin r)).sup (fun i => (a i).natAbs)) ha)
  let n := N + N
  have hn : N + N < ℓ ^ n := Nat.lt_pow_self hℓ
  refine ⟨n, fun a ha b hb h => funext (fun i => ?_)⟩
  have hi : (a i : ZMod (ℓ ^ n)) = (b i : ZMod (ℓ ^ n)) := congrFun h i
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hi
  have hab : (b i - a i).natAbs < ℓ ^ n :=
    (Int.natAbs_sub_le _ _).trans_lt ((Nat.add_le_add (hN b hb i) (hN a ha i)).trans_lt hn)
  exact (Int.sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hab))).symm

/-- The coordinate ring maps from a torus to its ℓ-power torsion subschemes
have joint kernel zero, with no reducedness assumption on the base ring. -/
theorem eq_zero_of_toric_torsion_restriction
    {R : Type*} [CommRing R] {r ℓ : ℕ} (hℓ : 1 < ℓ)
    (f : AddMonoidAlgebra R (Fin r → ℤ))
    (h : ∀ n : ℕ, AddMonoidAlgebra.mapDomainRingHom R (modToricExponent r (ℓ ^ n)) f = 0) :
    f = 0 := by
  classical
  obtain ⟨n, hn⟩ := exists_injOn_modToricExponent hℓ f.coeff.support
  have hz : Finsupp.mapDomain (modToricExponent r (ℓ ^ n)) f.coeff = 0 :=
    congrArg AddMonoidAlgebra.coeff (h n)
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.mapDomain_injOn (f.coeff.support : Set (Fin r → ℤ)) hn
  · exact Set.Subset.rfl
  · simp
  · rw [hz, AddMonoidAlgebra.coeff_zero, Finsupp.mapDomain_zero]

open CategoryTheory AlgebraicGeometry Limits

/-- The split torus in its Laurent coordinate presentation over a ring. -/
abbrev affineToricScheme (R : Type*) [CommRing R] (r : ℕ) : Scheme :=
  Spec (.of (AddMonoidAlgebra R (Fin r → ℤ)))

/-- The closed embedding of the subgroup of a split torus killed by `m`. -/
def affineToricTorsionι (R : Type*) [CommRing R] (r m : ℕ) :
    Spec (.of (AddMonoidAlgebra R (Fin r → ZMod m))) ⟶ affineToricScheme R r :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R (modToricExponent r m)))

/-- A closed subscheme containing every member of the ℓ-power torsion family
equals the original torus, including over a nonreduced base ring. -/
theorem isIso_of_affineToricTorsion_factors
    {R : Type*} [CommRing R] {r ℓ : ℕ} (hℓ : 1 < ℓ)
    {Z : Scheme} (i : Z ⟶ affineToricScheme R r) [IsClosedImmersion i]
    (h : ∀ n : ℕ, ∃ f, f ≫ i = affineToricTorsionι R r (ℓ ^ n)) :
    IsIso i := by
  obtain ⟨I, e, rfl⟩ := IsClosedImmersion.Spec_iff.mp ‹IsClosedImmersion i›
  have hI : I = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply Ideal.mem_bot.mpr
    apply eq_zero_of_toric_torsion_restriction hℓ x
    intro n
    obtain ⟨f, hf⟩ := h n
    let φ := Spec.preimage (f ≫ e.hom)
    have he : CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R
          (modToricExponent r (ℓ ^ n))) = CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ φ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Category.assoc]
      exact hf.symm
    have he' := congrArg (fun a => a.hom x) he
    simpa only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero] using he'
  subst I
  convert_to! IsIso (e.hom ≫ Spec.map (RingEquiv.quotientBot _).toCommRingCatIso.inv)
  infer_instance

/-- Morphisms from a split torus into a relatively separated scheme agree if
they agree on the joint family of ℓ-power torsion subschemes. -/
theorem affineToric_hom_ext_torsion
    {R : Type} [CommRing R] {r ℓ : ℕ} (hℓ : 1 < ℓ)
    {Y S : Scheme} (p : Y ⟶ S) [IsSeparated p]
    (f g : affineToricScheme R r ⟶ Y) (he : f ≫ p = g ≫ p)
    (h : ∀ n : ℕ, affineToricTorsionι R r (ℓ ^ n) ≫ f =
      affineToricTorsionι R r (ℓ ^ n) ≫ g) : f = g := by
  let X := Over.mk (f ≫ p)
  let Y' := Over.mk p
  let f' : X ⟶ Y' := Over.homMk f rfl
  let g' : X ⟶ Y' := Over.homMk g he.symm
  haveI : IsSeparated Y'.hom := ‹IsSeparated p›
  haveI : IsIso (equalizer.ι f' g').left := by
    apply isIso_of_affineToricTorsion_factors hℓ
    intro n
    let d := affineToricTorsionι R r (ℓ ^ n)
    let W := Over.mk (d ≫ X.hom)
    let d' : W ⟶ X := Over.homMk d rfl
    have hd : d' ≫ f' = d' ≫ g' := Over.OverMorphism.ext (h n)
    exact ⟨(equalizer.lift d' hd).left,
      congrArg Over.Hom.left (equalizer.lift_ι d' hd)⟩
  apply (cancel_epi (equalizer.ι f' g').left).mp
  exact congrArg Over.Hom.left (equalizer.condition f' g')

/-- Two maps over a locally finite type, formally unramified morphism
agree if they agree after a surjective change of source. In particular,
a nilpotent thickening does not change the equality test. -/
theorem hom_eq_of_surjective_precomp_of_formallyUnramified
    {X Y Z S : Scheme} (p : Y ⟶ S) [LocallyOfFiniteType p] [FormallyUnramified p]
    (f g : X ⟶ Y) (he : f ≫ p = g ≫ p) (a : Z ⟶ X) [Surjective a]
    (ha : a ≫ f = a ≫ g) : f = g := by
  let X' := Over.mk (f ≫ p)
  let Y' := Over.mk p
  let Z' := Over.mk (a ≫ X'.hom)
  let f' : X' ⟶ Y' := Over.homMk f rfl
  let g' : X' ⟶ Y' := Over.homMk g he.symm
  let a' : Z' ⟶ X' := Over.homMk a rfl
  let i := equalizer.ι f' g'
  haveI : IsOpenImmersion i.left := by
    refine MorphismProperty.of_isPullback
      ((Limits.isPullback_equalizer_prod f' g').map (Over.forget S)).flip ?_
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
      (Over.prodLeftIsoPullback Y' Y').hom]
    have hdiag : IsOpenImmersion (pullback.diagonal Y'.hom) :=
      show IsOpenImmersion (pullback.diagonal p) from inferInstance
    convert! hdiag
    ext1 <;> simp [← Over.comp_left]
  have ha' : a' ≫ f' = a' ≫ g' := Over.OverMorphism.ext ha
  let l := equalizer.lift a' ha'
  have hl : l.left ≫ i.left = a := congrArg Over.Hom.left (equalizer.lift_ι a' _)
  haveI : Surjective i.left := ⟨fun x => by
    obtain ⟨z, hz⟩ := a.surjective x
    refine ⟨l.left z, ?_⟩
    rwa [← Scheme.Hom.comp_apply, hl]⟩
  haveI : IsIso i.left := (isIso_iff_isOpenImmersion_and_surjective i.left).mpr
    ⟨inferInstance, inferInstance⟩
  apply (cancel_epi i.left).mp
  exact congrArg Over.Hom.left (equalizer.condition f' g')

#print axioms eq_zero_of_toric_torsion_restriction
#print axioms affineToric_hom_ext_torsion
#print axioms hom_eq_of_surjective_precomp_of_formallyUnramified

end SZRaynaud
