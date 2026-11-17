/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Finite prime spectra make the localization at an actual selected prime
an ACTUAL single-element localization. This is the finite-presentation
bridge for the DVR-stage refinement, not an assumption that raw R' is a
DVR or that connected/one-special-point spectra manufacture Mono.
-/
import Mathlib
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Maximal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

-- Finite-spectrum stage derivation and DVR/FF/fibre/factorization are owned
-- by Lane3's LocalStage consumer. Only the nonduplicated finite-prime
-- localization construction is supplied here.

/-- Select an actual finite-product element avoiding p and killing all
    primes not contained in p. Its single-element localization IS the
    prime localization, with its actual B-algebra map. -/
theorem exists_away_isLocalization_atPrime
    (B : Type u) [CommRing B] [Finite (PrimeSpectrum B)] (p : Ideal B) [p.IsPrime] :
    ∃ s : B, s ∉ p ∧ IsLocalization.AtPrime (Localization.Away s) p := by
  classical
  letI : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  let bad : Finset (PrimeSpectrum B) := Finset.univ.filter fun q => ¬q.asIdeal ≤ p
  have hex (q : bad) : ∃ x : B, x ∈ q.val.asIdeal ∧ x ∉ p := by
    have h := (Finset.mem_filter.mp q.property).2
    change ¬∀ x : B, x ∈ q.val.asIdeal → x ∈ p at h
    push_neg at h
    exact h
  let x : bad → B := fun q => Classical.choose (hex q)
  have hxq (q : bad) : x q ∈ q.val.asIdeal := (Classical.choose_spec (hex q)).1
  have hxp (q : bad) : x q ∉ p := (Classical.choose_spec (hex q)).2
  let s : B := ∏ q : bad, x q
  have hs : s ∉ p := by
    change s ∈ p.primeCompl
    exact p.primeCompl.prod_mem fun q _ => hxp q
  have hbad (q : PrimeSpectrum B) (hq : q ∈ bad) : s ∈ q.asIdeal := by
    have hd : x ⟨q, hq⟩ ∣ s := Finset.dvd_prod_of_mem x (Finset.mem_univ _)
    exact q.asIdeal.mem_of_dvd hd (hxq ⟨q, hq⟩)
  let C := Localization.Away s
  have hun (r : B) (hr : r ∈ p.primeCompl) : IsUnit (algebraMap B C r) := by
    by_contra hunit
    have hspan : Ideal.span {algebraMap B C r} ≠ (⊤ : Ideal C) :=
      Ideal.span_singleton_ne_top hunit
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {algebraMap B C r}) hspan
    let Q : PrimeSpectrum B := PrimeSpectrum.comap (algebraMap B C) ⟨m, hm.isPrime⟩
    have hrQ : r ∈ Q.asIdeal := hle (Ideal.subset_span rfl)
    have hsQ : s ∉ Q.asIdeal := by
      intro h
      change algebraMap B C s ∈ m at h
      exact hm.ne_top (m.eq_top_of_isUnit_mem h (IsLocalization.Away.algebraMap_isUnit s))
    by_cases hQ : Q.asIdeal ≤ p
    · exact hr (hQ hrQ)
    · have hQb : Q ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩
      exact hsQ (hbad Q hQb)
  have hle : Submonoid.powers s ≤ p.primeCompl := by
    rintro _ ⟨n, rfl⟩
    exact p.primeCompl.pow_mem hs n
  exact ⟨s, hs, IsLocalization.of_le (M := Submonoid.powers s) p.primeCompl hle hun⟩

#print axioms exists_away_isLocalization_atPrime

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
