import Mathlib
import ZInQKernel.HDecomp.Objects

/-!
# av-b1, III: T8 (`PkgI3.PoincareReducibility`) from Poincaré's theorem in Milne's form

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task av-b1, 2026-11-13).

The kernel's leaf T8, `PkgI3.PoincareReducibility`, is the form of Poincaré complete
reducibility used at step E1: over a field of characteristic `0`, if `End⁰(A)` is a division
algebra (`EndDivision A`) and `f : A → J` is a nonzero homomorphism, there are `Z` and `g : Z → J`
with `(f, g) : A × Z → J` an isogeny (finite and surjective). It is a consequence, not the literal
published statement. This file proves

* `poincareReducibility_of_pieces : PoincareComplement → ImageFactorization →
    SimpleSurjIsogeny → PkgI3.PoincareReducibility`

where `PoincareComplement` is Poincaré's theorem in the published form (an abelian subvariety
`B ⊆ J` has a complement `Z` with `B × Z → J` an isogeny), and the other two are textbook facts
about images and kernels of homomorphisms. The glue proved here: `f = i ∘ h` gives
`(f, g) = (i, g) ∘ (h × 1_Z)`, and `h × 1_Z` is finite and surjective when `h` is (base change).

The kernel's objects are written `_root_.PkgI3.…`, so that the file can be copied over a renamed
copy (`_root_.PkgI3 → _root_.HDec.PkgI3`, as in leaf-fold3's `mk_abvarbc.py`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AVB1

/-- **Poincaré complete reducibility, complement form** (published theorem). J. S. Milne,
*Abelian varieties*, in Cornell–Silverman (eds.), *Arithmetic Geometry* (1986), Prop. 12.1
(UNVERIFIED locator; over any field): for an abelian subvariety `B` of an abelian variety `J`
there is an abelian subvariety `Z ⊆ J` such that `B × Z → J`, `(b, z) ↦ b + z`, is an isogeny.
Over an algebraically closed field: D. Mumford, *Abelian varieties* (1970), §19, Thm 1
(UNVERIFIED locator: `B ∩ Z` finite and `B + Z = J`). Stated here with "abelian subvariety" as a
homomorphism `i : B → J` that is a closed immersion, in characteristic `0`, and without the
conclusion that `g : Z → J` is a closed immersion (so weaker than the published statement). -/
def PoincareComplement : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (J B : _root_.PkgI3.AbVar k)
    (i : _root_.PkgI3.AbVar.Hom B J), IsClosedImmersion i.hom.left →
    ∃ (Z : _root_.PkgI3.AbVar k) (g : _root_.PkgI3.AbVar.Hom Z J),
      _root_.PkgI3.AbVar.IsIsogenyMor (fst B.X Z.X ≫ i.hom * snd B.X Z.X ≫ g.hom)

/-- **The image of a homomorphism is an abelian subvariety** (textbook; GLUE-level composite).
Over a field of characteristic `0`, every homomorphism `f : A → J` of abelian varieties factors
as `f = i ∘ h` with `h : A → B` a surjective homomorphism and `i : B → J` a homomorphism that is
a closed immersion, `B` an abelian variety. Sources (UNVERIFIED locators): the image `f(A)` is
closed (`A` proper), reduced and irreducible, a subgroup; a reduced group scheme of finite type
over a field of characteristic `0` is smooth (Cartier; Mumford, *Abelian varieties*, §11, Thm 1);
geometric integrality passes to the image of the geometrically integral `A`; Milne 1986 §8
(images of homomorphisms are abelian subvarieties). -/
def ImageFactorization : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A J : _root_.PkgI3.AbVar k)
    (f : _root_.PkgI3.AbVar.Hom A J),
    ∃ (B : _root_.PkgI3.AbVar k) (h : _root_.PkgI3.AbVar.Hom A B)
      (i : _root_.PkgI3.AbVar.Hom B J),
      Surjective h.hom.left ∧ IsClosedImmersion i.hom.left ∧ f.hom = h.hom ≫ i.hom

/-- **A nonzero surjective homomorphism out of a simple abelian variety is an isogeny**
(textbook; GLUE-level composite). Over a field of characteristic `0`, if `End⁰(A)` is a division
algebra (`EndDivision A`) and `h : A → B` is a nonzero surjective homomorphism, then `h` is finite
(and surjective). Sources (UNVERIFIED locators): `(ker h)⁰_red` is an abelian subvariety of `A`
(characteristic `0`); it is not `A` since `h ≠ 0`; it is `0` because a proper nonzero abelian
subvariety would give, by Poincaré (Mumford §19 Thm 1, Cor. 1; Milne 1986 Prop. 12.1) and an
isogeny quasi-inverse, a nonzero endomorphism of `A` that is not surjective; a surjective
homomorphism with finite kernel is finite (Milne 1986, Prop. 7.1; Mumford §6, Application 1). -/
def SimpleSurjIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A B : _root_.PkgI3.AbVar k), _root_.PkgI3.EndDivision A →
    ∀ h : _root_.PkgI3.AbVar.Hom A B, h ≠ 0 → Surjective h.hom.left →
      _root_.PkgI3.AbVar.IsIsogenyMor h.hom

section Glue

variable {k : Type} [Field k]

/-- `1 ≫ i = 1` for a homomorphism `i`. -/
theorem one_comp_hom {A B J : _root_.PkgI3.AbVar k} (i : _root_.PkgI3.AbVar.Hom B J) :
    (1 : A.X ⟶ B.X) ≫ i.hom = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

/-- `h × 1_Z` is finite and surjective when `h` is. -/
theorem isIsogenyMor_whiskerRight {X Y : Over (Spec (CommRingCat.of k))} (h : X ⟶ Y)
    (Z : Over (Spec (CommRingCat.of k))) (hh : _root_.PkgI3.AbVar.IsIsogenyMor h) :
    _root_.PkgI3.AbVar.IsIsogenyMor (h ▷ Z) := by
  obtain ⟨h1, h2⟩ := hh
  refine ⟨?_, ?_⟩
  · rw [Over.whiskerRight_left]
    exact MorphismProperty.pullbackMap (P := @IsFinite.{0}) h1
      (inferInstance : IsFinite (𝟙 Z.left)) (Over.w h).symm (Category.id_comp _).symm
  · rw [Over.whiskerRight_left]
    haveI : MorphismProperty.IsStableUnderComposition @Surjective.{0} :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    exact MorphismProperty.pullbackMap (P := @Surjective.{0}) h2
      (inferInstance : Surjective (𝟙 Z.left)) (Over.w h).symm (Category.id_comp _).symm

/-- Isogeny-type maps compose. -/
theorem isIsogenyMor_comp {X Y W : Over (Spec (CommRingCat.of k))} (a : X ⟶ Y) (b : Y ⟶ W)
    (ha : _root_.PkgI3.AbVar.IsIsogenyMor a) (hb : _root_.PkgI3.AbVar.IsIsogenyMor b) :
    _root_.PkgI3.AbVar.IsIsogenyMor (a ≫ b) := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  refine ⟨?_, ?_⟩
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance

end Glue

/-- **T8 from Poincaré's theorem (complement form) and two textbook facts.** -/
theorem poincareReducibility_of_pieces (hP : PoincareComplement) (hI : ImageFactorization)
    (hS : SimpleSurjIsogeny) : _root_.PkgI3.PoincareReducibility := by
  intro k _ _ A J hA f hf
  obtain ⟨B, h, i, hsurj, hci, hfac⟩ := hI k A J f
  have hh : h ≠ 0 := by
    rintro rfl
    apply hf
    apply _root_.PkgI3.AbVar.Hom.ext'
    rw [hfac, _root_.PkgI3.AbVar.Hom.hom_zero, _root_.PkgI3.AbVar.Hom.hom_zero, one_comp_hom]
  have hiso := hS k A B hA h hh hsurj
  obtain ⟨Z, g, hm⟩ := hP k J B i hci
  refine ⟨Z, g, ?_⟩
  have heq : fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom =
      (h.hom ▷ Z.X) ≫ (fst B.X Z.X ≫ i.hom * snd B.X Z.X ≫ g.hom) := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, whiskerRight_fst, whiskerRight_snd,
      Category.assoc, hfac]
  rw [heq]
  exact isIsogenyMor_comp _ _ (isIsogenyMor_whiskerRight _ _ hiso) hm

end ZInQ.Contrib.AVB1
