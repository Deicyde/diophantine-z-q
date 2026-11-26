import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Basic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

variable {C : Type*} [Category C] [Preadditive C]

private def sequenceArrow (n : ℕ) : op (n + 1) ⟶ op n :=
  (homOfLE (Nat.le_succ n)).op

/-- The objects of an inverse sequence, indexed as a product family. -/
abbrev towerObjects (F : ℕᵒᵖ ⥤ C) (n : ℕ) : C := F.obj (op n)

variable (F : ℕᵒᵖ ⥤ C) [HasProduct (towerObjects F)]

/-- The literal difference between the identity and the shifted transition
on the categorical product. -/
noncomputable def towerSubShift : (∏ᶜ towerObjects F) ⟶ (∏ᶜ towerObjects F) :=
  Pi.lift (fun n => Pi.π (towerObjects F) n -
    Pi.π (towerObjects F) (n + 1) ≫ F.map (sequenceArrow n))

lemma towerSubShift_π (n : ℕ) :
    towerSubShift F ≫ Pi.π (towerObjects F) n = Pi.π (towerObjects F) n -
      Pi.π (towerObjects F) (n + 1) ≫ F.map (sequenceArrow n) :=
  Pi.lift_comp_π _ n

private lemma comp_towerSubShift_π {T : C} (f : T ⟶ ∏ᶜ towerObjects F) (n : ℕ) :
    (f ≫ towerSubShift F) ≫ Pi.π (towerObjects F) n =
      (f ≫ Pi.π (towerObjects F) n) -
        ((f ≫ Pi.π (towerObjects F) (n + 1)) ≫ F.map (sequenceArrow n)) := by
  rw [Category.assoc, towerSubShift_π, Preadditive.comp_sub, ← Category.assoc]

/-- From a cone over the inverse sequence to the product with the same legs. -/
noncomputable def towerConeToProduct (c : Cone F) : c.pt ⟶ ∏ᶜ towerObjects F :=
  Pi.lift (fun n => c.π.app (op n))

omit [Preadditive C] in
lemma towerConeToProduct_π (c : Cone F) (n : ℕ) :
    towerConeToProduct F c ≫ Pi.π (towerObjects F) n = c.π.app (op n) :=
  Pi.lift_comp_π _ n

lemma towerConeToProduct_subShift (c : Cone F) :
    towerConeToProduct F c ≫ towerSubShift F = 0 := by
  apply Pi.hom_ext
  intro n
  rw [comp_towerSubShift_π, towerConeToProduct_π, towerConeToProduct_π,
    c.w (sequenceArrow n), sub_self, Limits.zero_comp]

omit [Preadditive C] [HasProduct (towerObjects F)] in
private lemma compatible_of_next {T : C} (l : ∀ n : ℕ, T ⟶ F.obj (op n))
    (h : ∀ n, l (n + 1) ≫ F.map (sequenceArrow n) = l n) :
    ∀ (n m : ℕ) (hmn : m ≤ n), l n ≫ F.map (homOfLE hmn).op = l m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have he : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    rw [show (homOfLE hm).op = 𝟙 (op (0 : ℕ)) from Subsingleton.elim _ _,
      F.map_id, Category.comp_id]
  | succ n ih =>
    intro m hmn
    by_cases hm : m = n + 1
    · subst m
      rw [show (homOfLE hmn).op = 𝟙 (op (n + 1)) from Subsingleton.elim _ _,
        F.map_id, Category.comp_id]
    · have hle : m ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hmn hm)
      have harrow : (homOfLE hmn).op = sequenceArrow n ≫ (homOfLE hle).op :=
        Subsingleton.elim _ _
      rw [harrow, F.map_comp, ← Category.assoc, h n, ih m hle]

private noncomputable def compatibleConeOfSubShiftZero {T : C}
    (k : T ⟶ ∏ᶜ towerObjects F) (hk : k ≫ towerSubShift F = 0) : Cone F where
  pt := T
  π := {
    app j := k ≫ Pi.π (towerObjects F) j.unop
    naturality i j f := by
      have hnext (n : ℕ) : (k ≫ Pi.π (towerObjects F) (n + 1)) ≫ F.map (sequenceArrow n) =
          k ≫ Pi.π (towerObjects F) n := by
        have hcomp := comp_towerSubShift_π F k n
        rw [hk, Limits.zero_comp] at hcomp
        exact (sub_eq_zero.mp hcomp.symm).symm
      have h := compatible_of_next F (fun n => k ≫ Pi.π (towerObjects F) n)
        hnext i.unop j.unop (leOfHom f.unop)
      have he : (homOfLE (leOfHom f.unop)).op = f := Subsingleton.elim _ _
      rw [he] at h
      change 𝟙 T ≫ (k ≫ Pi.π (towerObjects F) j.unop) = (k ≫ Pi.π (towerObjects F) i.unop) ≫ F.map f
      exact (Category.id_comp _).trans h.symm }

/-- A limit of an inverse sequence is the kernel of the product difference,
with no assumption about surjectivity of the difference. -/
noncomputable def towerLimitIsKernel (c : Cone F) (hc : IsLimit c) :
    IsLimit (KernelFork.ofι (towerConeToProduct F c) (towerConeToProduct_subShift F c)) := by
  let lift {T : C} (k : T ⟶ ∏ᶜ towerObjects F) (hk : k ≫ towerSubShift F = 0) : T ⟶ c.pt :=
    hc.lift (compatibleConeOfSubShiftZero F k hk)
  refine KernelFork.IsLimit.ofι _ _ (@lift) ?_ ?_
  · intro T k hk
    apply Pi.hom_ext
    intro n
    let p := Pi.π (towerObjects F) n
    let a := towerConeToProduct F c
    have hl : lift k hk ≫ c.π.app (op n) = k ≫ p :=
      hc.fac (compatibleConeOfSubShiftZero F k hk) (op n)
    exact (Category.assoc (lift k hk) a p).trans
      ((congrArg (fun g => lift k hk ≫ g) (towerConeToProduct_π F c n)).trans hl)
  · intro T k hk f hf
    apply hc.hom_ext
    intro n
    let p := Pi.π (towerObjects F) n.unop
    let a := towerConeToProduct F c
    have hp : a ≫ p = c.π.app n := towerConeToProduct_π F c n.unop
    have hl : lift k hk ≫ c.π.app n = k ≫ p := hc.fac (compatibleConeOfSubShiftZero F k hk) n
    exact (congrArg (fun g => f ≫ g) hp.symm).trans
      ((Category.assoc f a p).symm.trans
        ((congrArg (fun g : T ⟶ ∏ᶜ towerObjects F => g ≫ p) hf).trans hl.symm))

end RC53.EllAdic
