/-
Global unramified-extension endpoint for the Kronecker–Weber reduction.
Uses the pinned Mathlib discriminant/ramification theorem; no local field,
local Kronecker–Weber, global class-field or desired embedding premise is hidden.
-/
module

public import Mathlib.NumberTheory.NumberField.ExistsRamified

/-!
# The unramified global endpoint over `ℚ`

The arithmetic elimination step is global: a Galois number field unramified at
every finite prime has degree one. This does not assert that a candidate field
built elsewhere is unramified; the exact hypothesis supplying that step remains
visible. In particular unramifiedness of an extension over a *cyclotomic* base
is not silently substituted for unramifiedness over `ℚ`.
-/

public section

set_option autoImplicit false

namespace ZInQ.Contrib.KroneckerWeber

open scoped NumberField

/-- A Galois number field unramified at every finite rational prime has degree
one over `ℚ`. The input and the rational prime quantifiers use the actual ring
of integers and the original rational scalar map. -/
theorem finrank_eq_one_of_unramified_at_all_finite_primes
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (hU : ∀ (p : ℕ), p.Prime → ∀ (P : Ideal (𝓞 L)) [P.IsPrime],
      (p : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt ℤ P) :
    Module.finrank ℚ L = 1 := by
  by_contra hL
  have hdeg : 1 < Module.finrank ℚ L := by
    have hpos := Module.finrank_pos (R := ℚ) (M := L)
    omega
  obtain ⟨p, hp, hram⟩ :=
    NumberField.exists_not_isUnramifiedAt_int_of_isGalois (𝒪 := 𝓞 L) hdeg
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ |>.isMaximal (by
      simpa using hpZ.ne_zero)
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 L) (Ideal.span {(p : ℤ)})
  have : P.IsPrime := hP.isPrime
  have hpP : (p : 𝓞 L) ∈ P := by
    have hzP : (algebraMap ℤ (𝓞 L) (p : ℤ)) ∈ P := by
      change (p : ℤ) ∈ P.under ℤ
      rw [← hPp.over]
      exact Ideal.mem_span_singleton_self _
    simpa only [map_natCast] using hzP
  exact hram P inferInstance hpP (hU p hp P hpP)

/-- The same global degree-one endpoint with no Galois assumption: unramifiedness
at every actual maximal ideal of the ring of integers suffices. -/
theorem finrank_eq_one_of_unramified_at_all_integer_maximals
    (L : Type*) [Field L] [NumberField L]
    (hU : ∀ (P : Ideal (𝓞 L)) [P.IsMaximal], Algebra.IsUnramifiedAt ℤ P) :
    Module.finrank ℚ L = 1 := by
  by_contra hL
  obtain ⟨P, hP, hram⟩ := NumberField.exists_not_isUnramifiedAt_int (𝒪 := 𝓞 L) hL
  have : P.IsMaximal := hP
  exact hram (hU P)

end ZInQ.Contrib.KroneckerWeber
