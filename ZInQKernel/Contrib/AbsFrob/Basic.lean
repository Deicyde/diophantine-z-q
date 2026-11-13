import Mathlib

-- Adopted by task frob-contrib from scratch/afr-absfrob/AbsFrobDef.lean (task afr-absfrob), namespace `AbsFrobDef`, unchanged.

/-!
# afr-absfrob: the absolute Frobenius of a scheme of characteristic `p`

Construction (not in Mathlib 4.35): for a scheme `X` with `(p : Γ(X, ⊤)) = 0`, `fr p X` is the
identity on the underlying space and `s ↦ s ^ p` on every ring of sections.
-/

noncomputable section

namespace AbsFrobDef

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

variable (p : ℕ) [hp : Fact p.Prime]

/-- `x ↦ x ^ p` as a ring endomorphism of a commutative ring in which `p = 0` (the ring may be
trivial, so no `CharP` instance is assumed). -/
def powHom (R : Type*) [CommRing R] (h : (p : R) = 0) : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow _
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.out.ne_zero
  map_add' x y := by
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim _ _
    · have := (CharP.charP_iff_prime_eq_zero hp.out).2 h
      exact add_pow_char x y p

@[simp] theorem powHom_apply (R : Type*) [CommRing R] (h : (p : R) = 0) (x : R) :
    powHom p R h x = x ^ p := rfl

omit hp in
/-- `p = 0` in every ring of sections of `X` if it is `0` in the global sections. -/
theorem natCast_sections {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) :
    (p : Γ(X, U)) = 0 := by
  have := congrArg (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom hX
  rwa [map_natCast, map_zero] at this

/-- The Frobenius on the structure presheaf. -/
def frobC (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    X.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat (𝟙 (X : TopCat))).obj X.presheaf where
  app U := CommRingCat.ofHom (powHom p _ (natCast_sections p hX U.unop))
  naturality U V i := by
    ext x
    exact (map_pow (X.presheaf.map i).hom x p).symm

/-- The absolute Frobenius as a morphism of presheafed spaces. -/
def frobPSh (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 _
  c := frobC p X hX

/-- The stalk map of the absolute Frobenius is `a ↦ a ^ p`. -/
theorem frob_stalkMap (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (x : X)
    (a : X.presheaf.stalk x) :
    ((frobPSh p X hX).stalkMap x).hom a = a ^ p := by
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  have := PresheafedSpace.stalkMap_germ_apply (frobPSh p X hX) U x hxU s
  erw [this]
  show X.presheaf.germ U x hxU (s ^ p) = _
  rw [map_pow]

/-- **The absolute Frobenius** `Fr_X : X ⟶ X` of a scheme with `p = 0` on `X`: the identity on
the underlying space, `s ↦ s ^ p` on sections (local on stalks since `a ^ p` a unit forces `a` a
unit). -/
def fr (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) : X ⟶ X :=
  Scheme.Hom.mk
    { toHom := frobPSh p X hX
      prop := fun x => ⟨fun a ha => by
        rw [frob_stalkMap p X hX x a] at ha
        exact (isUnit_pow_iff hp.out.ne_zero).mp ha⟩ }

@[simp] theorem fr_base (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    (fr p X hX).base = 𝟙 _ := rfl

theorem fr_app (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) :
    (fr p X hX).app U = CommRingCat.ofHom (powHom p _ (natCast_sections p hX U)) := rfl

/-- **Naturality of the absolute Frobenius:** `f ≫ Fr_X = Fr_Y ≫ f` for every morphism
`f : Y ⟶ X` of schemes on which `p = 0`. -/
theorem fr_naturality {X Y : Scheme.{u}} (f : Y ⟶ X) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) : f ≫ fr p X hX = fr p Y hY ≫ f := by
  have hb : (f ≫ fr p X hX).base = (fr p Y hY ≫ f).base := by
    rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, fr_base, fr_base, Category.comp_id,
      Category.id_comp]
  refine Scheme.Hom.ext hb fun U => ?_
  rw [show (eqToHom (congr((Opens.map $hb.symm).obj U))).op =
      𝟙 (op ((Opens.map (f ≫ fr p X hX).base).obj U)) from
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app, fr_app, fr_app]
  ext s
  exact map_pow (f.app U).hom s p

omit hp in
theorem natCast_Spec (R : CommRingCat.{u}) (h : (p : R) = 0) : (p : Γ(Spec R, ⊤)) = 0 := by
  have := congrArg (Scheme.ΓSpecIso R).inv.hom h
  rwa [map_natCast, map_zero] at this

omit hp in
theorem natCast_of_hom {R : CommRingCat.{u}} (h : (p : R) = 0) {X : Scheme.{u}}
    (f : X ⟶ Spec R) : (p : Γ(X, ⊤)) = 0 := by
  have := congrArg f.appTop.hom (natCast_Spec p R h)
  rwa [map_natCast, map_zero] at this

/-- **The absolute Frobenius of an affine scheme** is `Spec` of `r ↦ r ^ p`. -/
theorem fr_Spec (R : CommRingCat.{u}) (h : (p : R) = 0) :
    fr p (Spec R) (natCast_Spec p R h) = Spec.map (CommRingCat.ofHom (powHom p R h)) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso R).hom, Scheme.ΓSpecIso_naturality]
  ext s
  exact map_pow (Scheme.ΓSpecIso R).hom.hom s p

end AbsFrobDef
