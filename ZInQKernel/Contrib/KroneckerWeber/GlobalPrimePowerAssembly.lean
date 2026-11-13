/-
Global common-conductor assembly with ACTUAL rational-prime inertia coverage.
This is additive after global-v1. The two arithmetic unramifiedness/cardinality
inputs remain explicit; no unrestricted T17 provider or local KW is assumed.
-/
module

public import ZInQKernel.Contrib.KroneckerWeber.GlobalMilne
public import ZInQKernel.Contrib.KroneckerWeber.GlobalConductor
public import ZInQKernel.Contrib.KroneckerWeber.GlobalRationalDiscriminant

/-!
# The positive prime-power conductor and its exact global embedding endpoint

The finite rational prime set, positive product level, one-prime-per-rational-
prime coverage and totient product are all constructed or proved here. For the
ACTUAL enlarged compositum one still needs global unramifiedness outside the
original set and actual inertia-cardinality bounds at its primes. The local KW,
completed-field/valuation and prime-to-p arithmetic suppliers must derive those
two inputs; they are not supplied by this conditional global theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace ZInQ.Contrib.KroneckerWeber

open NumberField IsDedekindDomain
open scoped NumberField

/-- The genuine positive common product level for a finite rational prime set. -/
def primePowerConductor (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (r : ℕ → ℕ) : ℕ+ :=
  ⟨∏ p ∈ S, p ^ r p, prime_power_conductor_pos S hS r⟩

/-- Exact original-field cyclotomic embedding once the ACTUAL compositum's two
arithmetic inputs are proved. Finite-family coverage and the totient identity
are derived, not added caller hypotheses. The positive level is constructed. -/
theorem nonempty_embedding_at_primePowerConductor_of_arithmetic
    (L : Type*) [Field L] [NumberField L] [IsAbelianGalois ℚ L]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (r : ℕ → ℕ)
    (hU : ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (Q : Ideal (𝓞 (cyclotomicCompositum L (primePowerConductor S hS r)))) [Q.IsPrime],
        (p : 𝓞 (cyclotomicCompositum L (primePowerConductor S hS r))) ∈ Q →
          Algebra.IsUnramifiedAt ℤ Q)
    (hB : ∀ p ∈ S,
      ∀ (Q : Ideal (𝓞 (cyclotomicCompositum L (primePowerConductor S hS r)))) [Q.IsPrime],
        (p : 𝓞 (cyclotomicCompositum L (primePowerConductor S hS r))) ∈ Q →
          Nat.card (Q.inertia
            ((cyclotomicCompositum L (primePowerConductor S hS r)) ≃ₐ[ℚ]
              (cyclotomicCompositum L (primePowerConductor S hS r)))) ≤ (p ^ r p).totient) :
    Nonempty (L →ₐ[ℚ] CyclotomicField (primePowerConductor S hS r : ℕ) ℚ) := by
  classical
  let n := primePowerConductor S hS r
  let E := cyclotomicCompositum L n
  have : NumberField E := numberField_cyclotomicCompositum L n
  have : IsAbelianGalois ℚ E := isAbelianGalois_cyclotomicCompositum L n
  obtain ⟨P, hP, hcover, _⟩ :=
    exists_rational_prime_inertia_cover_of_unramified_outside E S hS hU
  have hb (p : S) : Nat.card ((P p).asIdeal.inertia (E ≃ₐ[ℚ] E)) ≤
      (p.val ^ r p.val).totient := hB p.val p.property (P p).asIdeal (hP p)
  have hprod : (∏ p : S, (p.val ^ r p.val).totient) = (n : ℕ).totient := by
    change (∏ p : S, (p.val ^ r p.val).totient) = (∏ p ∈ S, p ^ r p).totient
    rw [totient_prime_power_conductor S hS r]
    exact (Finset.prod_subtype S (fun _ => Iff.rfl) (fun p => (p ^ r p).totient)).symm
  exact nonempty_embedding_of_compositum_inertia_bounds L n P hcover
    (fun p : S => (p.val ^ r p.val).totient) hb hprod

end ZInQ.Contrib.KroneckerWeber
