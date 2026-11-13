/-
Exact full-global-domain checks for the additive rational-prime coverage version.
This does not mutate the global-v1 packet and declares no unrestricted T17 provider.
-/
module

public import ZInQKernel.Contrib.KroneckerWeber.GlobalPrimePowerAssembly

public section

set_option autoImplicit false

namespace ZInQ.Contrib.KroneckerWeber.RationalDiagnostics

open IsDedekindDomain
open scoped NumberField

example : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M],
    (∀ σ τ : M ≃ₐ[ℚ] M, σ * τ = τ * σ) →
      ∃ P : rationalRamificationSet M → HeightOneSpectrum (𝓞 M),
        (∀ p : rationalRamificationSet M, (p.val : 𝓞 M) ∈ (P p).asIdeal) ∧
        (∀ Q : HeightOneSpectrum (𝓞 M),
          Q.asIdeal.inertia (M ≃ₐ[ℚ] M) ≤
            ⨆ p : rationalRamificationSet M, (P p).asIdeal.inertia (M ≃ₐ[ℚ] M)) ∧
        (⨆ p : rationalRamificationSet M, (P p).asIdeal.inertia (M ≃ₐ[ℚ] M)) = ⊤ := by
  intro M _ _ _ hcomm
  have : IsMulCommutative (M ≃ₐ[ℚ] M) := ⟨⟨hcomm⟩⟩
  have : IsAbelianGalois ℚ M := { }
  exact exists_rational_discriminant_inertia_family M

example (r : ℕ → ℕ) : (primePowerConductor ∅ (by simp) r : ℕ) = 1 := by
  simp [primePowerConductor]

end ZInQ.Contrib.KroneckerWeber.RationalDiagnostics

#check @ZInQ.Contrib.KroneckerWeber.exists_rational_discriminant_inertia_family
#check @ZInQ.Contrib.KroneckerWeber.nonempty_embedding_at_primePowerConductor_of_arithmetic

#print axioms ZInQ.Contrib.KroneckerWeber.exists_rational_prime_below_integer_prime
#print axioms ZInQ.Contrib.KroneckerWeber.global_inertia_eq_bot_of_unramified
#print axioms ZInQ.Contrib.KroneckerWeber.global_inertia_eq_of_common_rational_prime
#print axioms ZInQ.Contrib.KroneckerWeber.exists_actual_integer_primes_above_finset
#print axioms ZInQ.Contrib.KroneckerWeber.exists_rational_prime_inertia_cover_of_unramified_outside
#print axioms ZInQ.Contrib.KroneckerWeber.rationalRamificationSet
#print axioms ZInQ.Contrib.KroneckerWeber.prime_of_mem_rationalRamificationSet
#print axioms ZInQ.Contrib.KroneckerWeber.globally_unramified_outside_rationalRamificationSet
#print axioms ZInQ.Contrib.KroneckerWeber.exists_rational_discriminant_inertia_family
#print axioms ZInQ.Contrib.KroneckerWeber.primePowerConductor
#print axioms ZInQ.Contrib.KroneckerWeber.nonempty_embedding_at_primePowerConductor_of_arithmetic
