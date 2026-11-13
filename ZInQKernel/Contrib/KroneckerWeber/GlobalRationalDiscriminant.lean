/-
The finite RATIONAL ramification set of an actual number field over Q.
This is additive after the frozen global-v1 proof packet, not a refresh of its
sources or its validation. It provides no local KW or cyclotomic inertia bounds.
-/
module

public import ZInQKernel.Contrib.KroneckerWeber.GlobalRationalInertia
public import Mathlib.Data.Nat.PrimeFin

/-!
# Actual global inertia family at rational discriminant primes

The selected rational-prime set is finite and is defined from the ORIGINAL field's
nonzero discriminant. All-prime unramifiedness outside it is proved from the actual
discriminant/unramifiedness theorem. In an abelian extension, one actual integer
prime above each rational prime covers every original global inertia subgroup.
The later cyclotomic compositum must separately be shown unramified outside the
SAME original set before this family can be used at its chosen conductor.
-/

@[expose] public section

set_option autoImplicit false

namespace ZInQ.Contrib.KroneckerWeber

open NumberField IsDedekindDomain
open scoped NumberField

/-- The finite set of rational primes dividing the absolute actual discriminant. -/
noncomputable def rationalRamificationSet (M : Type*) [Field M] [NumberField M] : Finset ℕ :=
  (NumberField.discr M).natAbs.primeFactors

theorem prime_of_mem_rationalRamificationSet
    (M : Type*) [Field M] [NumberField M] (p : ℕ) (hp : p ∈ rationalRamificationSet M) :
    p.Prime := Nat.prime_of_mem_primeFactors hp

/-- Every actual integer prime above a rational prime outside the discriminant
set is globally unramified over `ℤ`. No Galois assumption is needed here. -/
theorem globally_unramified_outside_rationalRamificationSet
    (M : Type*) [Field M] [NumberField M] (p : ℕ) (hp : p.Prime)
    (hmiss : p ∉ rationalRamificationSet M) (P : Ideal (𝓞 M)) [P.IsPrime]
    (hpP : (p : 𝓞 M) ∈ P) : Algebra.IsUnramifiedAt ℤ P := by
  have hD0 : (NumberField.discr M).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero M)
  have hndvd : ¬ (p : ℤ) ∣ NumberField.discr M := by
    intro hdvd
    have habs : p ∣ (NumberField.discr M).natAbs := by
      obtain ⟨z, hz⟩ := hdvd
      refine ⟨z.natAbs, ?_⟩
      rw [hz, Int.natAbs_mul, Int.natAbs_natCast]
    exact hmiss (Nat.mem_primeFactors.mpr ⟨hp, habs, hD0⟩)
  have hpZ : Prime (p : ℤ) := (Nat.prime_iff_prime_int).mp hp
  exact ((NumberField.not_dvd_discr_iff_forall_mem M (𝓞 M) hpZ).mp hndvd) P
    (inferInstance : P.IsPrime) (by simpa only [Int.cast_natCast] using hpP)

/-- For every abelian number field, one ACTUAL integer prime above each rational
discriminant prime covers every actual global inertia group, and these groups
generate the original Galois group. This is closed global rational-prime coverage,
not the cyclotomic degree/cardinality upper bounds required by full T17. -/
theorem exists_rational_discriminant_inertia_family
    (M : Type*) [Field M] [NumberField M] [IsAbelianGalois ℚ M] :
    ∃ P : rationalRamificationSet M → HeightOneSpectrum (𝓞 M),
      (∀ p : rationalRamificationSet M, (p.val : 𝓞 M) ∈ (P p).asIdeal) ∧
      (∀ Q : HeightOneSpectrum (𝓞 M),
        Q.asIdeal.inertia (M ≃ₐ[ℚ] M) ≤
          ⨆ p : rationalRamificationSet M, (P p).asIdeal.inertia (M ≃ₐ[ℚ] M)) ∧
      (⨆ p : rationalRamificationSet M, (P p).asIdeal.inertia (M ≃ₐ[ℚ] M)) = ⊤ :=
  exists_rational_prime_inertia_cover_of_unramified_outside M (rationalRamificationSet M)
    (fun p hp => prime_of_mem_rationalRamificationSet M p hp)
    (fun p hp hm P _ hP => globally_unramified_outside_rationalRamificationSet M p hp hm P hP)

end ZInQ.Contrib.KroneckerWeber
