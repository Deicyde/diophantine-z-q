/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; a copy is in docs/research/t13-skolem-noether.md.
Authors: The Tau Ceti contributors

Adapted for Lean/Mathlib 4.35.0 by Metamate (2026-11-13): isolated namespace,
removed examples and unused centrality results; retained both simplicity orientations.
Source: TauCetiProject/TauCeti, revision 61090fff281d0c6cece0176aa8436ab748b53048,
TauCeti/Algebra/CentralSimple/TensorProduct.lean.
-/
import ZInQKernel.Contrib.SkolemNoether.TensorCoordinates
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TwoSidedIdeal.Operations

namespace ZInQ.Contrib.SkolemNoether

open Module
open scoped TensorProduct

section Auxiliary

variable {K A B : Type*} [CommSemiring K] [Ring A] [Semiring B] [Algebra K A] [Algebra K B]

/-- Simplicity of `A` permits rescaling one nonzero coordinate to `1`,
without enlarging the support. -/
private lemma exists_mem_repr_eq_one [IsSimpleRing A] {ι : Type*} (𝓑 : Basis ι K B)
    {I : TwoSidedIdeal (A ⊗[K] B)} {S : Finset ι} {i₀ : ι} {y₀ : A ⊗[K] B} (hy₀I : y₀ ∈ I)
    (hy₀S : ∀ j ∉ S, (Algebra.TensorProduct.basis A 𝓑).repr y₀ j = 0)
    (hne : (Algebra.TensorProduct.basis A 𝓑).repr y₀ i₀ ≠ 0) :
    ∃ y ∈ I, (∀ j ∉ S, (Algebra.TensorProduct.basis A 𝓑).repr y j = 0) ∧
      (Algebra.TensorProduct.basis A 𝓑).repr y i₀ = 1 := by
  classical
  set carrier : Set A :=
    {a | ∃ y ∈ I, (∀ j ∉ S, (Algebra.TensorProduct.basis A 𝓑).repr y j = 0) ∧
      (Algebra.TensorProduct.basis A 𝓑).repr y i₀ = a}
  have hzero : (0 : A) ∈ carrier := ⟨0, I.zero_mem, by simp, by simp⟩
  have hadd : ∀ {a a' : A}, a ∈ carrier → a' ∈ carrier → a + a' ∈ carrier := by
    rintro _ _ ⟨y, hy, hys, rfl⟩ ⟨z, hz, hzs, rfl⟩
    exact ⟨y + z, I.add_mem hy hz, fun j hj => by simp [hys j hj, hzs j hj], by simp⟩
  have hneg : ∀ {a : A}, a ∈ carrier → -a ∈ carrier := by
    rintro _ ⟨y, hy, hys, rfl⟩
    exact ⟨-y, I.neg_mem hy, fun j hj => by simp [hys j hj], by simp⟩
  have hmulleft : ∀ {a a' : A}, a' ∈ carrier → a * a' ∈ carrier := by
    rintro a _ ⟨y, hy, hys, rfl⟩
    exact ⟨(a ⊗ₜ[K] (1 : B)) * y, I.mul_mem_left _ _ hy,
      fun j hj => by simp [hys j hj], by simp⟩
  have hmulright : ∀ {a a' : A}, a ∈ carrier → a * a' ∈ carrier := by
    rintro _ a' ⟨y, hy, hys, rfl⟩
    exact ⟨y * (a' ⊗ₜ[K] (1 : B)), I.mul_mem_right _ _ hy,
      fun j hj => by rw [basis_repr_mul_tmul_one, hys j hj, zero_mul],
      basis_repr_mul_tmul_one ..⟩
  have hone : (1 : A) ∈ carrier := by
    have hmem : (Algebra.TensorProduct.basis A 𝓑).repr y₀ i₀ ∈ carrier := ⟨y₀, hy₀I, hy₀S, rfl⟩
    have := IsSimpleRing.one_mem_of_ne_zero_mem
      (TwoSidedIdeal.mk' carrier hzero hadd hneg hmulleft hmulright) hne
      ((TwoSidedIdeal.mem_mk' ..).mpr hmem)
    exact (TwoSidedIdeal.mem_mk' ..).mp this
  exact hone

/-- A minimal-support element with one coordinate `1` commutes with `A ⊗ 1`:
every commutator has strictly smaller support. -/
private lemma commute_tmul_one_of_repr_eq_one {ι : Type*} (𝓑 : Basis ι K B)
    {I : TwoSidedIdeal (A ⊗[K] B)} {S : Finset ι} {i₀ : ι} (hi₀ : i₀ ∈ S) {y : A ⊗[K] B}
    (hyI : y ∈ I) (hyS : ∀ j ∉ S, (Algebra.TensorProduct.basis A 𝓑).repr y j = 0)
    (hy1 : (Algebra.TensorProduct.basis A 𝓑).repr y i₀ = 1)
    (hmin : ∀ z ∈ I, ((Algebra.TensorProduct.basis A 𝓑).repr z).support.card < S.card → z = 0)
    (a : A) : Commute (a ⊗ₜ[K] (1 : B)) y := by
  classical
  have hsupp : ((Algebra.TensorProduct.basis A 𝓑).repr
      ((a ⊗ₜ[K] (1 : B)) * y - y * (a ⊗ₜ[K] (1 : B)))).support ⊆ S.erase i₀ := by
    intro j hj
    simp only [Finsupp.mem_support_iff, map_sub, Finsupp.sub_apply,
      tmul_one_mul_eq_smul, map_smul, Finsupp.smul_apply, smul_eq_mul,
      basis_repr_mul_tmul_one] at hj
    by_cases hjS : j ∈ S
    · exact Finset.mem_erase.mpr ⟨by rintro rfl; simp [hy1] at hj, hjS⟩
    · simp [hyS j hjS] at hj
  have hz : (a ⊗ₜ[K] (1 : B)) * y - y * (a ⊗ₜ[K] (1 : B)) = 0 :=
    hmin _ (I.sub_mem (I.mul_mem_left _ _ hyI) (I.mul_mem_right _ _ hyI))
      (lt_of_le_of_lt (Finset.card_le_card hsupp) (Finset.card_erase_lt_of_mem hi₀))
  exact sub_eq_zero.mp hz

end Auxiliary

variable {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]

/-- A central simple algebra tensored with a simple algebra is simple.
No finite-dimensionality or separability is used. -/
theorem tensorProduct_simple [Algebra.IsCentral K A] [IsSimpleRing A] [IsSimpleRing B] :
    IsSimpleRing (A ⊗[K] B) := by
  classical
  have : Nontrivial (A ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left K A B
      (FaithfulSMul.algebraMap_injective K B)
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  rw [or_iff_not_imp_left, ← I.one_mem_iff]
  intro hI
  let 𝓑 := Basis.ofVectorSpace K B
  obtain ⟨x, hxI, hx0 : x ≠ 0⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : ⊥ < I)
  obtain ⟨y₀, hmin⟩ := exists_minimalFor_of_wellFoundedLT (fun y => y ∈ I ∧ y ≠ 0)
    (fun y => ((Algebra.TensorProduct.basis A 𝓑).repr y).support.card) ⟨x, hxI, hx0⟩
  obtain ⟨hy₀I, hy₀0⟩ := hmin.prop
  set S := ((Algebra.TensorProduct.basis A 𝓑).repr y₀).support
  obtain ⟨i₀, hi₀⟩ : S.Nonempty := Finsupp.support_nonempty_iff.mpr (by simpa using hy₀0)
  obtain ⟨y, hyI, hyS, hy1⟩ := exists_mem_repr_eq_one 𝓑 hy₀I
    (fun j hj => Finsupp.notMem_support_iff.mp hj) (Finsupp.mem_support_iff.mp hi₀)
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at hy1
    exact zero_ne_one hy1
  have hcomm := commute_tmul_one_of_repr_eq_one 𝓑 hi₀ hyI hyS hy1
    (fun z hz hlt => by_contra fun hz0 => hmin.not_lt ⟨hz, hz0⟩ hlt)
  obtain ⟨b, rfl⟩ := forall_commute_tmul_one_iff.mp hcomm
  have hb : b ≠ 0 := by rintro rfl; exact hy0 (by simp)
  have honeB : (1 : B) ∈
      I.comap (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B) :=
    IsSimpleRing.one_mem_of_ne_zero_mem _ hb
      ((TwoSidedIdeal.mem_comap _).mpr (by simpa using hyI))
  rw [TwoSidedIdeal.mem_comap] at honeB
  simpa [Algebra.TensorProduct.one_def] using honeB

/-- The same simplicity theorem with the central algebra on the right.
This is the orientation needed for the full T13 embedding statement. -/
theorem tensorProduct_simple_right [IsSimpleRing A] [Algebra.IsCentral K B] [IsSimpleRing B] :
    IsSimpleRing (A ⊗[K] B) :=
  IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm K B A).toRingEquiv
    (tensorProduct_simple (K := K) (A := B) (B := A))

end ZInQ.Contrib.SkolemNoether
