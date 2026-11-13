/-
Finite rational-prime indexing of ACTUAL global inertia groups.
This is additive to the frozen global-v1 packet. No completed Galois adapter,
local norm theorem, local KW or arbitrary conductor bound is implemented here.
-/
module

public import ZInQKernel.Contrib.KroneckerWeber.GlobalInertiaFinite
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Global inertia coverage by one actual prime over each rational prime

The inertia groups of primes over the same rational prime are equal in an abelian
extension: transitivity supplies the actual conjugating automorphism and
commutativity makes the conjugation map trivial. Outside a finite rational prime
set, a supplied genuine global unramifiedness assertion gives trivial inertia.
This discharges the finite-family coverage part, not the local conductor bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace ZInQ.Contrib.KroneckerWeber

open NumberField IsDedekindDomain
open scoped NumberField IsMulCommutative Pointwise

/-- An actual nonzero integer prime lies over some rational prime. -/
theorem exists_rational_prime_below_integer_prime
    (M : Type*) [Field M] [NumberField M] (P : HeightOneSpectrum (𝓞 M)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 M) ∈ P.asIdeal := by
  have hq0 : P.asIdeal.under ℤ ≠ ⊥ := by
    intro h
    exact P.ne_bot (Ideal.eq_bot_of_under_eq_bot h)
  obtain ⟨a, ha : P.asIdeal.under ℤ = Ideal.span {a}⟩ :=
    IsPrincipalIdealRing.principal (P.asIdeal.under ℤ)
  have ha0 : a ≠ 0 := by
    intro h
    exact hq0 (ha.trans (by simp [h]))
  have hap : Prime a := by
    rw [← Ideal.span_singleton_prime ha0, ← ha]
    infer_instance
  have haP : algebraMap ℤ (𝓞 M) a ∈ P.asIdeal := by
    have hmem : a ∈ P.asIdeal.under ℤ := by
      rw [ha]
      exact Ideal.mem_span_singleton_self a
    exact hmem
  refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.mp hap, ?_⟩
  have hmem : algebraMap ℤ (𝓞 M) (a.natAbs : ℤ) ∈ P.asIdeal :=
    P.asIdeal.mem_of_dvd (map_dvd (algebraMap ℤ (𝓞 M)) a.associated_natAbs.dvd) haP
  simpa only [map_natCast] using hmem

/-- Genuine global unramifiedness over `ℤ` makes the actual inertia subgroup trivial. -/
theorem global_inertia_eq_bot_of_unramified
    (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M]
    (P : Ideal (𝓞 M)) [P.IsPrime] (hU : Algebra.IsUnramifiedAt ℤ P) :
    P.inertia (M ≃ₐ[ℚ] M) = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  rw [card_global_inertia_eq_ramificationIdx]
  exact Ideal.ramificationIdx_eq_one_iff.mpr hU

/-- Two actual primes above the same rational prime have the SAME inertia subgroup
in an abelian global Galois group, not merely the same cardinality. -/
theorem global_inertia_eq_of_common_rational_prime
    (M : Type*) [Field M] [NumberField M] [IsAbelianGalois ℚ M]
    (p : ℕ) (hp : p.Prime) (P Q : Ideal (𝓞 M)) [P.IsPrime] [Q.IsPrime]
    (hP : (p : 𝓞 M) ∈ P) (hQ : (p : 𝓞 M) ∈ Q) :
    P.inertia (M ≃ₐ[ℚ] M) = Q.inertia (M ≃ₐ[ℚ] M) := by
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hpZ : Prime (p : ℤ) := (Nat.prime_iff_prime_int).mp hp
  have : P.LiesOver q := (Ideal.liesOver_span_iff Ideal.IsPrime.ne_top' hpZ).mpr
    (by simpa only [map_natCast] using hP)
  have : Q.LiesOver q := (Ideal.liesOver_span_iff Ideal.IsPrime.ne_top' hpZ).mpr
    (by simpa only [map_natCast] using hQ)
  obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup q P Q (M ≃ₐ[ℚ] M)
  rw [Ideal.inertia_smul]
  have hnormal : (P.inertia (M ≃ₐ[ℚ] M)).Normal := inferInstance
  exact ((Subgroup.normal_iff_map_conj_eq).mp hnormal σ).symm

/-- Choose one ACTUAL upper integer prime above each rational prime in a finite set. -/
theorem exists_actual_integer_primes_above_finset
    (M : Type*) [Field M] [NumberField M]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ P : S → HeightOneSpectrum (𝓞 M), ∀ p : S, (p.val : 𝓞 M) ∈ (P p).asIdeal := by
  classical
  have hex (p : S) : ∃ P : HeightOneSpectrum (𝓞 M), (p.val : 𝓞 M) ∈ P.asIdeal := by
    let q : Ideal ℤ := Ideal.span {(p.val : ℤ)}
    have hpZ : Prime (p.val : ℤ) := (Nat.prime_iff_prime_int).mp (hS p.val p.property)
    have hq0 : q ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hpZ.ne_zero
    have : q.IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
    have : q.IsMaximal := (inferInstance : q.IsPrime).isMaximal hq0
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) q
    have : P.IsPrime := hP.isPrime
    have : P.LiesOver q := hPQ
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hq0 ⟨hP.isPrime, hPQ⟩
    have hpP : algebraMap ℤ (𝓞 M) (p.val : ℤ) ∈ P :=
      (Ideal.mem_of_liesOver P q _).mp (Ideal.mem_span_singleton_self _)
    exact ⟨⟨P, hP.isPrime, hP0⟩, by simpa only [map_natCast] using hpP⟩
  choose P hP using hex
  exact ⟨P, hP⟩

/-- If all actual primes outside `S` are globally unramified, one actual prime above
each rational prime in `S` covers EVERY global inertia subgroup. This is a genuine
global coverage derivation, not an assumed generator family or local statement. -/
theorem exists_rational_prime_inertia_cover_of_unramified_outside
    (M : Type*) [Field M] [NumberField M] [IsAbelianGalois ℚ M]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hU : ∀ p : ℕ, p.Prime → p ∉ S → ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime],
      (p : 𝓞 M) ∈ Q → Algebra.IsUnramifiedAt ℤ Q) :
    ∃ P : S → HeightOneSpectrum (𝓞 M),
      (∀ p : S, (p.val : 𝓞 M) ∈ (P p).asIdeal) ∧
      (∀ Q : HeightOneSpectrum (𝓞 M),
        Q.asIdeal.inertia (M ≃ₐ[ℚ] M) ≤ ⨆ p : S, (P p).asIdeal.inertia (M ≃ₐ[ℚ] M)) ∧
      (⨆ p : S, (P p).asIdeal.inertia (M ≃ₐ[ℚ] M)) = ⊤ := by
  classical
  obtain ⟨P, hP⟩ := exists_actual_integer_primes_above_finset M S hS
  have hcover (Q : HeightOneSpectrum (𝓞 M)) :
      Q.asIdeal.inertia (M ≃ₐ[ℚ] M) ≤ ⨆ p : S, (P p).asIdeal.inertia (M ≃ₐ[ℚ] M) := by
    obtain ⟨p, hp, hpQ⟩ := exists_rational_prime_below_integer_prime M Q
    by_cases hpS : p ∈ S
    · let i : S := ⟨p, hpS⟩
      rw [global_inertia_eq_of_common_rational_prime M p hp Q.asIdeal (P i).asIdeal hpQ (hP i)]
      exact le_iSup (fun j : S => (P j).asIdeal.inertia (M ≃ₐ[ℚ] M)) i
    · rw [global_inertia_eq_bot_of_unramified M Q.asIdeal (hU p hp hpS Q.asIdeal hpQ)]
      exact bot_le
  refine ⟨P, hP, hcover, top_unique ?_⟩
  rw [← globalInertiaSpan_eq_top M, globalInertiaSpan_def]
  exact iSup_le hcover

end ZInQ.Contrib.KroneckerWeber
