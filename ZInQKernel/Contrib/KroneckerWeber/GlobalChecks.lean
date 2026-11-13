/-
Exact quantified-type, exceptional-case and recursive dependency checks for the
additive GLOBAL Kronecker–Weber work. No unrestricted T17 provider is declared.
The original eight partial modules and their checks remain byte-immutable.
-/
module

public import ZInQKernel.Contrib.KroneckerWeber.GlobalMilne
public import ZInQKernel.Contrib.KroneckerWeber.GlobalConductor
public import Mathlib.NumberTheory.Cyclotomic.Gal

public section

set_option autoImplicit false

namespace ZInQ.Contrib.KroneckerWeber.GlobalDiagnostics

open IsDedekindDomain
open scoped NumberField

-- The global inertia generator statement is CLOSED on the full finite-Galois domain.
example : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M],
    (⨆ P : HeightOneSpectrum (NumberField.RingOfIntegers M),
      P.asIdeal.inertia (M ≃ₐ[ℚ] M)) = ⊤ := by
  intro M _ _ _
  rw [← globalInertiaSpan_def]
  exact globalInertiaSpan_eq_top M

-- The cyclic generation reduction uses the exact original commutativity hypothesis,
-- with no exponent-two, radical or desired-embedding condition.
example : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) →
      ∃ (ι : Type) (_ : Fintype ι) (F : ι → IntermediateField ℚ L),
        (∀ i, IsGalois ℚ (F i) ∧ IsCyclic ((F i) ≃ₐ[ℚ] (F i))) ∧ (⨆ i, F i) = ⊤ := by
  intro L _ _ _ hcomm
  exact exists_cyclic_subextensions_of_comm L hcomm

-- Positive level one is the genuine rational subfield in the same algebraic closure.
example : cyclotomicLayer 1 = (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
  IntermediateField.finrank_eq_one_iff.mp (by simpa using finrank_cyclotomicLayer 1)

-- The conductor product includes p=2 and exponent zero, with the actual totient factors.
example : (2 ^ 3 * 3 ^ 1 : ℕ).totient = (2 ^ 3 : ℕ).totient * (3 ^ 1 : ℕ).totient :=
  Nat.totient_mul (prime_powers_coprime Nat.prime_two Nat.prime_three (by decide) 3 1)

example : (2 ^ 0 * 3 ^ 0 : ℕ).totient = (2 ^ 0 : ℕ).totient * (3 ^ 0 : ℕ).totient :=
  Nat.totient_mul (prime_powers_coprime Nat.prime_two Nat.prime_three (by decide) 0 0)

-- Adverse scope check: an actual allowed abelian number field need not have
-- exponent-two automorphisms. This is NOT a counterexample to full Kronecker–Weber.
example : ¬ ∀ σ : CyclotomicField 5 ℚ ≃ₐ[ℚ] CyclotomicField 5 ℚ, σ ^ 2 = 1 := by
  have : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  let e : (CyclotomicField 5 ℚ ≃ₐ[ℚ] CyclotomicField 5 ℚ) ≃* (ZMod 5)ˣ :=
    IsCyclotomicExtension.autEquivPow _ (Polynomial.cyclotomic.irreducible_rat (by decide))
  let u : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩
  intro h
  have he := congrArg e (h (e.symm u))
  have hu : u ^ 2 = 1 := by
    simpa only [map_pow, MulEquiv.apply_symm_apply, map_one] using he
  exact (show u ^ 2 ≠ 1 from by decide) hu

end ZInQ.Contrib.KroneckerWeber.GlobalDiagnostics

#check @ZInQ.Contrib.KroneckerWeber.exists_cyclic_subextensions_of_comm
#check @ZInQ.Contrib.KroneckerWeber.globalInertiaSpan_eq_top
#check @ZInQ.Contrib.KroneckerWeber.ramificationIdx_under_fixedField_eq_one_of_inertia_le
#check @ZInQ.Contrib.KroneckerWeber.exists_global_inertia_degree_bound
#check @ZInQ.Contrib.KroneckerWeber.nonempty_embedding_of_compositum_inertia_bounds

#print axioms ZInQ.Contrib.KroneckerWeber.exists_cyclic_subextensions
#print axioms ZInQ.Contrib.KroneckerWeber.exists_cyclic_subextensions_of_comm
#print axioms ZInQ.Contrib.KroneckerWeber.cyclotomicLayer
#print axioms ZInQ.Contrib.KroneckerWeber.cyclotomicLayer_isCyclotomic
#print axioms ZInQ.Contrib.KroneckerWeber.cyclotomicLayerEquiv
#print axioms ZInQ.Contrib.KroneckerWeber.cyclotomicLayer_le_of_dvd
#print axioms ZInQ.Contrib.KroneckerWeber.le_cyclotomicLayer_of_embedding
#print axioms ZInQ.Contrib.KroneckerWeber.exists_cyclotomicLayer_containing_family
#print axioms ZInQ.Contrib.KroneckerWeber.exists_positive_embedding_of_generating_subfields
#print axioms ZInQ.Contrib.KroneckerWeber.exists_positive_embedding_of_cyclic_subfield_input
#print axioms ZInQ.Contrib.KroneckerWeber.finrank_eq_one_of_unramified_at_all_finite_primes
#print axioms ZInQ.Contrib.KroneckerWeber.finrank_eq_one_of_unramified_at_all_integer_maximals
#print axioms ZInQ.Contrib.KroneckerWeber.subgroupProductMap
#print axioms ZInQ.Contrib.KroneckerWeber.subgroupProductMap_surjective
#print axioms ZInQ.Contrib.KroneckerWeber.card_le_prod_of_subgroup_generation
#print axioms ZInQ.Contrib.KroneckerWeber.finrank_cyclotomicLayer
#print axioms ZInQ.Contrib.KroneckerWeber.eq_cyclotomicLayer_of_degree_bound
#print axioms ZInQ.Contrib.KroneckerWeber.eq_cyclotomicLayer_of_subgroup_bounds
#print axioms ZInQ.Contrib.KroneckerWeber.ramificationIdx_under_fixedField_eq_one_of_inertia_le
#print axioms ZInQ.Contrib.KroneckerWeber.globalInertiaSpan
#print axioms ZInQ.Contrib.KroneckerWeber.globalInertiaSpan_def
#print axioms ZInQ.Contrib.KroneckerWeber.globalInertiaSpan_fixedField_unramified
#print axioms ZInQ.Contrib.KroneckerWeber.globalInertiaSpan_eq_top
#print axioms ZInQ.Contrib.KroneckerWeber.card_global_inertia_eq_ramificationIdx
#print axioms ZInQ.Contrib.KroneckerWeber.exists_finset_global_inertia_generating
#print axioms ZInQ.Contrib.KroneckerWeber.exists_global_inertia_degree_bound
#print axioms ZInQ.Contrib.KroneckerWeber.prime_powers_coprime
#print axioms ZInQ.Contrib.KroneckerWeber.prime_power_conductor_pos
#print axioms ZInQ.Contrib.KroneckerWeber.totient_prime_power_conductor
#print axioms ZInQ.Contrib.KroneckerWeber.rationalClosureEmbedding
#print axioms ZInQ.Contrib.KroneckerWeber.cyclotomicCompositum
#print axioms ZInQ.Contrib.KroneckerWeber.numberField_cyclotomicCompositum
#print axioms ZInQ.Contrib.KroneckerWeber.isAbelianGalois_cyclotomicCompositum
#print axioms ZInQ.Contrib.KroneckerWeber.nonempty_embedding_of_compositum_inertia_bounds
#print axioms GlobalDifferentTransport.ramificationIdx_fixedField_eq_card_inf
