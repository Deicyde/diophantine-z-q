import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Group.Subgroup.Ker

set_option autoImplicit false

open CategoryTheory CategoryTheory.Abelian

namespace RC53.EllAdic

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The actual induced homomorphism on first Ext, viewed in the kernel of
the next map in the same short complex. -/
noncomputable def extOneToNextKernel (T : C) (S : ShortComplex C) :
    Ext.{w} T S.X₁ 1 →+ ↥((Ext.mk₀ S.g).postcomp T (add_zero 1)).ker where
  toFun x := ⟨x.comp (Ext.mk₀ S.f) (add_zero 1), by
    change (x.comp (Ext.mk₀ S.f) (add_zero 1)).comp (Ext.mk₀ S.g) (add_zero 1) = 0
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, S.zero, Ext.mk₀_zero, Ext.comp_zero]⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero ((Ext.mk₀ S.f).postcomp T (add_zero 1))
  map_add' x y := by
    apply Subtype.ext
    exact map_add ((Ext.mk₀ S.f).postcomp T (add_zero 1)) x y

/-- When the degree-zero map induced by the last arrow is surjective, the
first Ext of the subobject identifies with the kernel of the corresponding
first Ext map. The forward map is induced by the original first arrow. -/
theorem extOneToNextKernel_bijective (T : C) (S : ShortComplex C) (hS : S.ShortExact)
    (h₀ : Function.Surjective ((Ext.mk₀ S.g).postcomp T (add_zero 0) :
      Ext.{w} T S.X₂ 0 →+ Ext.{w} T S.X₃ 0)) :
    Function.Bijective (extOneToNextKernel T S : Ext.{w} T S.X₁ 1 →+ _) := by
  have hzero (x : Ext.{w} T S.X₁ 1) (hx : extOneToNextKernel T S x = 0) : x = 0 := by
    have hx' : x.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := congrArg Subtype.val hx
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ T hS x hx' (zero_add 1)
    obtain ⟨b, hb⟩ := h₀ z
    change b.comp (Ext.mk₀ S.g) (add_zero 0) = z at hb
    rw [← hb, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero] at hz
    exact hz.symm
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  · intro y
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ T hS y.1 y.property
    exact ⟨x, Subtype.ext hx⟩

end RC53.EllAdic
