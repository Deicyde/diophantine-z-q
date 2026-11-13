/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; a copy is in docs/research/t13-skolem-noether.md.
Authors: The Tau Ceti contributors

Adapted for Lean/Mathlib 4.35.0 by Metamate (2026-11-13): isolated namespace;
retained only the enveloping-algebra action and the two linear-map lemmas used
by T13. Removed restricted-module and universal-property machinery.
Source: TauCetiProject/TauCeti, revision 61090fff281d0c6cece0176aa8436ab748b53048,
TauCeti/Algebra/CentralSimple/Bimodule.lean.
-/
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.RingTheory.TensorProduct.Maps

namespace ZInQ.Contrib.SkolemNoether

open scoped TensorProduct

variable {K A B : Type*} [CommSemiring K] [Semiring A] [Algebra K A]
  [Semiring B] [Algebra K B]

/-- The carrier `A` with left `B`-action through `f` and regular right `A`-action.
A separate carrier for each map lets both actions coexist. -/
def Bimodule (_f : B →ₐ[K] A) : Type _ := A

namespace Bimodule

variable (f : B →ₐ[K] A)

instance : AddCommMonoid (Bimodule f) := inferInstanceAs (AddCommMonoid A)
instance {A : Type*} [Ring A] [Algebra K A] (f : B →ₐ[K] A) : AddCommGroup (Bimodule f) :=
  inferInstanceAs (AddCommGroup A)
instance : Module K (Bimodule f) := inferInstanceAs (Module K A)
instance [Nontrivial A] : Nontrivial (Bimodule f) := inferInstanceAs (Nontrivial A)
instance [Module.Finite K A] : Module.Finite K (Bimodule f) :=
  inferInstanceAs (Module.Finite K A)

/-- The underlying ground-field vector space is unchanged. -/
def of : A ≃ₗ[K] Bimodule f := LinearEquiv.refl K A

/-- The enveloping-algebra representation: `b ⊗ op a` acts by `x ↦ f b * x * a`. -/
noncomputable def toEnd : B ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A :=
  (AlgHom.mulLeftRight K A).comp (Algebra.TensorProduct.map f (AlgHom.id K Aᵐᵒᵖ))

@[simp]
theorem toEnd_tmul_apply (b : B) (a : Aᵐᵒᵖ) (x : A) :
    toEnd f (b ⊗ₜ a) x = f b * x * a.unop := by
  simp [toEnd]

noncomputable instance : Module (B ⊗[K] Aᵐᵒᵖ) (Bimodule f) :=
  Module.compHom (M := A) (toEnd f).toRingHom

/-- The sole unfolding boundary for the transported action. -/
theorem smul_def (r : B ⊗[K] Aᵐᵒᵖ) (x : A) : r • of f x = of f (toEnd f r x) := rfl

instance : IsScalarTower K (B ⊗[K] Aᵐᵒᵖ) (Bimodule f) where
  smul_assoc c r x := by
    rw [← (of f).apply_symm_apply x, smul_def, smul_def, map_smul (toEnd f),
      LinearMap.smul_apply, map_smul (of f)]

@[simp]
theorem smul_of (b : B) (a : Aᵐᵒᵖ) (x : A) :
    (b ⊗ₜ a : B ⊗[K] Aᵐᵒᵖ) • of f x = of f (f b * x * a.unop) :=
  toEnd_tmul_apply f b a x

@[simp]
theorem symm_smul (b : B) (a : Aᵐᵒᵖ) (y : Bimodule f) :
    (of f).symm ((b ⊗ₜ a : B ⊗[K] Aᵐᵒᵖ) • y) = f b * (of f).symm y * a.unop :=
  toEnd_tmul_apply f b a ((of f).symm y)

section Map

variable {f g : B →ₐ[K] A}

/-- Right linearity makes a bimodule map left multiplication by its value at `1`. -/
theorem symm_apply_eq_symm_apply_one_mul
    (φ : Bimodule f →ₗ[B ⊗[K] Aᵐᵒᵖ] Bimodule g) (a : A) :
    (of g).symm (φ (of f a)) = (of g).symm (φ (of f 1)) * a := by
  have ha : of f a = (1 ⊗ₜ MulOpposite.op a : B ⊗[K] Aᵐᵒᵖ) • of f 1 := by
    rw [smul_of]; simp
  rw [ha, map_smul, symm_smul]
  simp

/-- Left linearity makes the value at `1` intertwine the two algebra maps. -/
theorem symm_apply_one_mul_eq_mul_symm_apply_one
    (φ : Bimodule f →ₗ[B ⊗[K] Aᵐᵒᵖ] Bimodule g) (b : B) :
    (of g).symm (φ (of f 1)) * f b = g b * (of g).symm (φ (of f 1)) := by
  set u : A := (of g).symm (φ (of f 1)) with hu
  have hu' : φ (of f 1) = of g u := by rw [hu]; simp
  have h1 : (b ⊗ₜ (1 : Aᵐᵒᵖ) : B ⊗[K] Aᵐᵒᵖ) • of f 1 = of f (f b) := by
    rw [smul_of]; simp
  calc u * f b = (of g).symm (φ (of f (f b))) :=
        (symm_apply_eq_symm_apply_one_mul φ (f b)).symm
    _ = (of g).symm (φ ((b ⊗ₜ (1 : Aᵐᵒᵖ) : B ⊗[K] Aᵐᵒᵖ) • of f 1)) := by rw [h1]
    _ = (of g).symm ((b ⊗ₜ (1 : Aᵐᵒᵖ) : B ⊗[K] Aᵐᵒᵖ) • φ (of f 1)) := by rw [map_smul]
    _ = (of g).symm ((b ⊗ₜ (1 : Aᵐᵒᵖ) : B ⊗[K] Aᵐᵒᵖ) • of g u) := by rw [hu']
    _ = g b * u := by rw [smul_of]; simp

/-- If a bimodule map hits `1`, its transported value at `1` has a right inverse. -/
theorem exists_symm_apply_one_mul_eq_one
    (φ : Bimodule f →ₗ[B ⊗[K] Aᵐᵒᵖ] Bimodule g) (h1 : of g 1 ∈ LinearMap.range φ) :
    ∃ v : A, (of g).symm (φ (of f 1)) * v = 1 := by
  obtain ⟨y, hy⟩ := h1
  refine ⟨(of f).symm y, ?_⟩
  have h := symm_apply_eq_symm_apply_one_mul φ ((of f).symm y)
  rw [LinearEquiv.apply_symm_apply, hy] at h
  simpa using h.symm

end Map
end Bimodule
end ZInQ.Contrib.SkolemNoether
