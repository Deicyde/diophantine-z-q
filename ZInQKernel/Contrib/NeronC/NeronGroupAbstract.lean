import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # neron-c: the group law of a Néron model comes from the mapping property (abstract part)

Task neron-c (2026-11-13). Leaf T41 is h5-neron's `ZInQ.H5Neron.NeronModelExists`: for an abelian
variety `A/K` and a number field `L ⊇ K`, `A_L` has a Néron model over `𝓞_L` in the project's
sense, a `GroupModel` (a smooth, separated, quasi-compact *group* scheme `𝒩` over `𝓞_L` with an
isomorphism of *group* schemes `𝒩_L ≅ A_L`) with the Néron mapping property for smooth test
schemes. The published theorem (Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.4 Thm. 3, with
Def. 1 of §1.2) produces a Néron model as a *scheme*; its group law is then derived from the
mapping property (BLR §1.2, the remark after Def. 1). This file proves that derivation in Lean, in
the abstract form `grpObjOfNeron` / `isMonHom_of_neron` (any functor `F`, any class `P` of test
objects closed under `⊗` and containing `𝟙_`), and reduces T41 to the scheme-level statement
`NeronSchemeModelExists`, which asks for no group structure. -/

namespace ZInQ.Contrib.NeronC

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section Abstract

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  (F : C ⥤ D) (P : C → Prop) (hP1 : P (𝟙_ C)) (hP2 : ∀ X Y : C, P X → P Y → P (X ⊗ Y))
  (N : C) (hN : P N) (A : D) [GrpObj A] (e : F.obj N ≅ A)
  (h : ∀ Y : C, P Y → Function.Bijective fun f : Y ⟶ N => F.map f ≫ e.hom)

/-- `Φ f = F f ≫ e`. -/
noncomputable def nPhi {F : C ⥤ D} {N : C} {A : D} (e : F.obj N ≅ A) {Y : C} (f : Y ⟶ N) : F.obj Y ⟶ A :=
  F.map f ≫ e.hom

include h in
/-- The inverse of `Φ` on a test object. -/
noncomputable def nPsi {Y : C} (hY : P Y) : (F.obj Y ⟶ A) → (Y ⟶ N) :=
  (Equiv.ofBijective _ (h Y hY)).symm

lemma nPhi_comp {Y Z : C} (f : Y ⟶ Z) (g : Z ⟶ N) : nPhi e (f ≫ g) = F.map f ≫ nPhi e g := by
  simp [nPhi]

lemma nPhi_nPsi {Y : C} (hY : P Y) (a : F.obj Y ⟶ A) : nPhi e (nPsi F P N A e h hY a) = a :=
  (Equiv.ofBijective _ (h Y hY)).apply_symm_apply a

include h in
lemma nPhi_inj {Y : C} (hY : P Y) {f g : Y ⟶ N} (hfg : nPhi e f = nPhi e g) : f = g :=
  (h Y hY).1 hfg

/-- **The group law on a Néron model**, transported from `A` through the mapping property. -/
@[instance_reducible]
noncomputable def grpObjOfNeron : GrpObj N where
  one := nPsi F P N A e h hP1 1
  mul := nPsi F P N A e h (hP2 N N hN hN) (nPhi e (fst N N) * nPhi e (snd N N))
  inv := nPsi F P N A e h hN (nPhi e (𝟙 N))⁻¹
  one_mul := by
    apply nPhi_inj F P N A e h (hP2 _ _ hP1 hN)
    simp only [nPhi_comp, nPhi_nPsi, comp_mul]
    simp only [← nPhi_comp]
    simp only [whiskerRight_fst, whiskerRight_snd, nPhi_comp, nPhi_nPsi, MonObj.comp_one,
      _root_.one_mul, leftUnitor_hom]
  mul_one := by
    apply nPhi_inj F P N A e h (hP2 _ _ hN hP1)
    simp only [nPhi_comp, nPhi_nPsi, comp_mul]
    simp only [← nPhi_comp]
    simp only [whiskerLeft_fst, whiskerLeft_snd, nPhi_comp, nPhi_nPsi, MonObj.comp_one,
      _root_.mul_one, rightUnitor_hom]
  mul_assoc := by
    apply nPhi_inj F P N A e h (hP2 _ _ (hP2 _ _ hN hN) hN)
    simp only [nPhi_comp, nPhi_nPsi, comp_mul]
    simp only [← nPhi_comp]
    simp only [whiskerRight_fst, whiskerRight_snd, whiskerLeft_fst, associator_hom_fst,
      whiskerLeft_snd, nPhi_comp, nPhi_nPsi, comp_mul, _root_.mul_assoc]
    simp only [← nPhi_comp]
    simp only [← Category.assoc, associator_hom_fst, associator_hom_snd_fst,
      associator_hom_snd_snd]
    simp only [Category.assoc, associator_hom_snd_fst, associator_hom_snd_snd]
  left_inv := by
    apply nPhi_inj F P N A e h hN
    simp only [nPhi_comp, nPhi_nPsi, comp_mul, MonObj.comp_one]
    simp only [← nPhi_comp, lift_fst, lift_snd]
    simp only [nPhi_nPsi]
    exact inv_mul_cancel (nPhi e (𝟙 N))
  right_inv := by
    apply nPhi_inj F P N A e h hN
    simp only [nPhi_comp, nPhi_nPsi, comp_mul, MonObj.comp_one]
    simp only [← nPhi_comp, lift_fst, lift_snd]
    simp only [nPhi_nPsi]
    exact mul_inv_cancel (nPhi e (𝟙 N))

/-- **The identification `e : F N ≅ A` is a homomorphism** for the transported group law on `N`
and the group law of `F N` induced by the monoidal functor `F`. -/
theorem isMonHom_of_neron [F.Monoidal] :
    letI := grpObjOfNeron F P hP1 hP2 N hN A e h
    letI : GrpObj (F.obj N) := Functor.grpObjObj
    IsMonHom e.hom := by
  letI := grpObjOfNeron F P hP1 hP2 N hN A e h
  letI : GrpObj (F.obj N) := Functor.grpObjObj
  have hη : F.map η[N] ≫ e.hom = 1 := nPhi_nPsi F P N A e h hP1 1
  have hμ : F.map μ[N] ≫ e.hom = nPhi e (fst N N) * nPhi e (snd N N) :=
    nPhi_nPsi F P N A e h (hP2 N N hN hN) _
  constructor
  · rw [Functor.obj.η_def, Category.assoc, hη, MonObj.comp_one, Hom.one_def,
      toUnit_unique (toUnit (𝟙_ D)) (𝟙 _), Category.id_comp]
  · rw [Functor.obj.μ_def, Category.assoc, hμ, MonObj.comp_mul, Hom.mul_def]
    simp only [nPhi, Functor.Monoidal.μ_fst_assoc, Functor.Monoidal.μ_snd_assoc]
    congr 1
    ext <;> simp

end Abstract

end ZInQ.Contrib.NeronC
