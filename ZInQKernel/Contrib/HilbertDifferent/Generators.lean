/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the source LICENSE.
Authors: The Tau Ceti contributors

Adapted from TauCetiProject/TauCeti at a6027b1d24fcb935c53bd5b50d11b40991cda418:
 RingTheory/Ideal/Inertia.lean, lines 47–69;
 FieldTheory/IntermediateField/Adjoin/EqTop.lean, lines 268–293;
 FieldTheory/Galois/Minpoly.lean, lines 50–79.
Only the generator criteria and derivative factorization are retained. Names and
imports are changed to this project and its existing Mathlib v4.35 pin.
See docs/research/t20-hilbert-different.md for the source license and scope.
-/
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Minpoly.ConjRootClass
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Localization.FractionRing

namespace ZInQ.Contrib.HilbertDifferent

/-- Testing inertia on algebra generators is equivalent to testing it on the whole ring. -/
theorem mem_inertia_iff_of_adjoin_eq_top {G S R : Type*} [Group G] [Ring S]
    [MulSemiringAction G S] [CommSemiring R] [Algebra R S] [SMulCommClass G R S]
    {I : Ideal S} [I.IsTwoSided] {s : Set S} (hs : Algebra.adjoin R s = ⊤) {σ : G} :
    σ ∈ I.inertia G ↔ ∀ x ∈ s, σ • x - x ∈ I := by
  rw [Ideal.mem_inertia]
  refine ⟨fun h x _ ↦ h x, fun h x ↦ ?_⟩
  have hx : x ∈ Algebra.adjoin R s := hs ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact h y hy
  | algebraMap r => simp
  | add y z _ _ hy hz =>
      rw [smul_add, add_sub_add_comm]
      exact add_mem hy hz
  | mul y z _ _ hy hz =>
      rw [smul_mul']
      exact I.mul_sub_mul_mem hy hz

/-- In a monogenic algebra a single displacement decides membership in every inertia group. -/
theorem mem_inertia_iff_of_adjoin_singleton_eq_top {G S R : Type*} [Group G] [Ring S]
    [MulSemiringAction G S] [CommSemiring R] [Algebra R S] [SMulCommClass G R S]
    {I : Ideal S} [I.IsTwoSided] {x : S} (hx : Algebra.adjoin R {x} = ⊤) {σ : G} :
    σ ∈ I.inertia G ↔ σ • x - x ∈ I := by
  simp [mem_inertia_iff_of_adjoin_eq_top hx]

/-- Only the identity can fix an algebra generator in a faithful action. -/
theorem eq_one_of_smul_generator_eq {G S R : Type*} [Group G] [Semiring S]
    [MulSemiringAction G S] [FaithfulSMul G S] [CommSemiring R] [Algebra R S]
    [SMulCommClass G R S] {x : S} (hx : Algebra.adjoin R {x} = ⊤)
    {σ : G} (hσ : σ • x = x) : σ = 1 := by
  apply MulSemiringAction.toAlgHom_injective R S
  exact AlgHom.ext_of_adjoin_eq_top hx (Set.eqOn_singleton.mpr (by simpa using hσ))

/-- Ring generation implies generation of the fraction field over any intervening base field. -/
theorem field_adjoin_eq_top_of_ring_adjoin_eq_top {R S K L : Type*} [CommSemiring R]
    [CommRing S] [Field K] [Field L] [Algebra R S] [Algebra R K] [Algebra R L]
    [Algebra S L] [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsFractionRing S L] {x : S} (hx : Algebra.adjoin R {x} = ⊤) :
    IntermediateField.adjoin K {algebraMap S L x} = ⊤ := by
  have hle : Algebra.adjoin R {x} ≤
      ((IntermediateField.adjoin K {algebraMap S L x}).toSubalgebra.restrictScalars R).comap
        (IsScalarTower.toAlgHom R S L) :=
    Algebra.adjoin_le (by
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact IntermediateField.subset_adjoin K _ (Set.mem_singleton _))
  refine eq_top_iff.mpr fun y _ ↦ ?_
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := S) y
  exact div_mem (hle (hx.ge Algebra.mem_top)) (hle (hx.ge Algebra.mem_top))

section GaloisPolynomial

open Polynomial IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The conjugates of a primitive element run through the Galois group exactly once. -/
theorem minpoly_map_eq_prod_X_sub_C_of_adjoin_eq_top {x : L} (hx : K⟮x⟯ = ⊤) :
    (minpoly K x).map (algebraMap K L) = ∏ σ : L ≃ₐ[K] L, (X - C (σ x)) := by
  classical
  have hinj : Function.Injective fun σ : L ≃ₐ[K] L ↦ σ x := fun σ τ h ↦
    AlgEquiv.coe_toAlgHom_injective <| AlgHom.ext_of_adjoin_eq_top
      ((adjoin_eq_top_iff_of_isAlgebraic fun y _ ↦ IsAlgebraic.of_finite K y).1 hx)
      (Set.eqOn_singleton.2 h)
  have hcarrier : (ConjRootClass.mk K x).carrier.toFinset =
      Finset.univ.image fun σ : L ≃ₐ[K] L ↦ σ x := by
    ext y
    simp [ConjRootClass.mem_carrier, isConjRoot_iff_exists_algEquiv]
  rw [← ConjRootClass.minpoly_mk, ConjRootClass.minpoly.map_eq_prod, hcarrier,
    Finset.prod_image hinj.injOn]

/-- The derivative at the primitive element is the product of all nonidentity displacements. -/
theorem aeval_derivative_minpoly_eq_prod_of_adjoin_eq_top [DecidableEq (L ≃ₐ[K] L)]
    {x : L} (hx : K⟮x⟯ = ⊤) :
    aeval x (derivative (minpoly K x)) =
      ∏ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), (x - σ x) := by
  rw [← eval_map_algebraMap, ← derivative_map,
    minpoly_map_eq_prod_X_sub_C_of_adjoin_eq_top hx, derivative_prod_finset, eval_finsetSum,
    Fintype.sum_eq_single 1]
  · simp [eval_prod]
  · intro σ hσ
    simp only [derivative_X_sub_C, mul_one, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hσ, Finset.mem_univ 1⟩) (by simp)

end GaloisPolynomial

end ZInQ.Contrib.HilbertDifferent
