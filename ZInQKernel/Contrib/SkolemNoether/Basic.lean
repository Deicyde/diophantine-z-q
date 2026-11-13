/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; a copy is in docs/research/t13-skolem-noether.md.
Authors: The Tau Ceti contributors

Adapted and extended for Lean/Mathlib 4.35.0 by Metamate (2026-11-13).
Source: TauCetiProject/TauCeti, revision 61090fff281d0c6cece0176aa8436ab748b53048,
TauCeti/Algebra/CentralSimple/SkolemNoether.lean, proof of `TauCeti.skolemNoether`.
IMPORTANT: that upstream declaration assumes centrality of the SOURCE. Here the
central-right tensor simplicity theorem supplies the full AMBIENT-central form.
No centrality or separability of the source is assumed.
-/
import ZInQKernel.Contrib.SkolemNoether.TensorSimple
import ZInQKernel.Contrib.SkolemNoether.ModuleClassification
import ZInQKernel.Contrib.SkolemNoether.Bimodule
import Mathlib.RingTheory.TensorProduct.Finite

namespace ZInQ.Contrib.SkolemNoether

open scoped TensorProduct

/-- **Skolem–Noether, full embedding form.** Any two algebra maps from a simple
finite-dimensional algebra into a central simple finite-dimensional algebra are
conjugate by one unit, uniformly on the whole source. The source need not be
central, and the maps need not be surjective. -/
theorem skolemNoether (K : Type*) {A B : Type*} [Field K]
    [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B]
    [FiniteDimensional K B] (f g : B →ₐ[K] A) :
    ∃ u : Aˣ, ∀ b : B, g b = (u : A) * f b * ((u⁻¹ : Aˣ) : A) := by
  have : FiniteDimensional K Aᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv K)
  -- Unlike the upstream Skolem–Noether statement, centrality is on the RIGHT
  -- factor, Aᵐᵒᵖ. Opposite preserves both centrality and simplicity.
  have : IsSimpleRing (B ⊗[K] Aᵐᵒᵖ) := tensorProduct_simple_right
  have hrank : Module.finrank K (Bimodule f) = Module.finrank K (Bimodule g) :=
    ((Bimodule.of f).symm.trans (Bimodule.of g)).finrank_eq
  obtain ⟨φ⟩ := nonempty_linearEquiv_of_finrank_eq (R := B ⊗[K] Aᵐᵒᵖ) K hrank
  set ψ : Bimodule f →ₗ[B ⊗[K] Aᵐᵒᵖ] Bimodule g := φ.toLinearMap with hψ
  have hψsurj : Function.Surjective ψ := by rw [hψ]; simpa using φ.surjective
  obtain ⟨v, huv⟩ := Bimodule.exists_symm_apply_one_mul_eq_one ψ (hψsurj _)
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  set u : A := (Bimodule.of g).symm (ψ (Bimodule.of f 1))
  have hUval : ((Units.mkOfMulEqOne u v huv : Aˣ) : A) = u := Units.val_mkOfMulEqOne huv
  have hUinv : (↑(Units.mkOfMulEqOne u v huv)⁻¹ : A) = v :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hUval]; exact huv)
  have hb : ∀ b : B, u * f b = g b * u :=
    Bimodule.symm_apply_one_mul_eq_mul_symm_apply_one ψ
  refine ⟨Units.mkOfMulEqOne u v huv, fun b ↦ ?_⟩
  rw [hUval, hUinv, hb b, mul_assoc, huv, mul_one]

/-- The exact closed, quantified T13 statement from research revision
`533aa66cc3485e21f2d90303e3a34f79d081722d`, `scratch/h-decomposition/Leaves.lean`.
This does not import that scratch file or assume its leaf as a hypothesis. -/
theorem t13 :
    ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
      [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
      (f g : B →ₐ[K] A), ∃ u : Aˣ, ∀ b : B, g b = (u : A) * f b * ((u⁻¹ : Aˣ) : A) := by
  intro K A B _ _ _ _ _ _ _ _ _ _ f g
  exact skolemNoether K f g

/-- The automorphism consequence is separate from, and derived from, full T13. -/
theorem exists_unit_conj_of_algEquiv (K : Type*) {A : Type*} [Field K]
    [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (e : A ≃ₐ[K] A) :
    ∃ u : Aˣ, ∀ a : A, e a = (u : A) * a * ((u⁻¹ : Aˣ) : A) :=
  skolemNoether K (AlgHom.id K A) e.toAlgHom

end ZInQ.Contrib.SkolemNoether
