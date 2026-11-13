/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; a copy is in docs/research/t13-skolem-noether.md.
Authors: The Tau Ceti contributors

Adapted for Lean/Mathlib 4.35.0 by Metamate (2026-11-13): selected only the tensor
coordinate and centralizer lemmas needed for T13, and isolated their namespace.
Source: TauCetiProject/TauCeti, revision 61090fff281d0c6cece0176aa8436ab748b53048,
TauCeti/Algebra/TensorProduct/Mul.lean and TauCeti/Algebra/Central/TensorProduct.lean.
-/
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Free

namespace ZInQ.Contrib.SkolemNoether

open scoped TensorProduct

section Coordinates

variable {K A B ι : Type*} [CommSemiring K] [Semiring A] [Algebra K A]
  [NonAssocSemiring B] [Module K B] [SMulCommClass K B B] [IsScalarTower K B B]

/-- Left multiplication by `a ⊗ 1` is the left `A`-action. -/
@[simp]
theorem tmul_one_mul_eq_smul (a : A) (x : A ⊗[K] B) :
    (a ⊗ₜ[K] (1 : B)) * x = a • x := by
  simpa [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul'] using smul_one_mul a x

/-- Right multiplication by `a ⊗ 1` multiplies each left coordinate on the right. -/
@[simp]
theorem basis_repr_mul_tmul_one (𝓑 : Module.Basis ι K B) (a : A) (x : A ⊗[K] B) (j : ι) :
    (Algebra.TensorProduct.basis A 𝓑).repr (x * (a ⊗ₜ[K] (1 : B))) j =
      (Algebra.TensorProduct.basis A 𝓑).repr x j * a := by
  induction x using TensorProduct.inductionOn with
  | tmul a' b => simp [mul_assoc, ← Algebra.commutes]
  | add x y hx hy => simp [add_mul, hx, hy]

end Coordinates

section Centralizer

variable {K A B : Type*} [CommSemiring K] [Semiring A] [Semiring B]
  [Algebra K A] [Algebra K B]

/-- For a central algebra, the centralizer of `A ⊗ 1` is `1 ⊗ B`. -/
theorem forall_commute_tmul_one_iff [Module.Free K B] [Algebra.IsCentral K A]
    {x : A ⊗[K] B} :
    (∀ a : A, Commute (a ⊗ₜ[K] (1 : B)) x) ↔ ∃ b : B, x = 1 ⊗ₜ[K] b := by
  refine ⟨fun h => ?_, ?_⟩
  · have hx : x ∈ Subalgebra.centralizer K
        ((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).range : Set (A ⊗[K] B)) := by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ ⟨a, rfl⟩
      simpa using (h a).eq
    rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct,
      Algebra.IsCentral.center_eq_bot] at hx
    obtain ⟨y, rfl⟩ := hx
    clear h
    induction y using TensorProduct.inductionOn with
    | tmul a b =>
      obtain ⟨k, hk⟩ := Algebra.mem_bot.mp a.2
      exact ⟨k • b, by
        simp [← hk, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]⟩
    | add y z hy hz =>
      obtain ⟨b, hb⟩ := hy
      obtain ⟨c, hc⟩ := hz
      exact ⟨b + c, by rw [map_add, hb, hc, TensorProduct.tmul_add]⟩
  · rintro ⟨b, rfl⟩ a
    simp [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul]

end Centralizer

end ZInQ.Contrib.SkolemNoether
