import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-! # Principal localizations in semilocal Dedekind domains -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {C : Type*} [CommRing C]

/-- Separate the chosen maximal ideal from all the others by one element. -/
theorem exists_local_separator [IsDedekindDomain C]
    (hf : {P : Ideal C | P.IsMaximal}.Finite) (q : Ideal C) [hq : q.IsMaximal] :
    ∃ s : C, s ∉ q ∧ ∀ P : Ideal C, P.IsMaximal → P ≠ q → s ∈ P := by
  classical
  let T : Set (Ideal C) := {P | P.IsMaximal ∧ P ≠ q}
  have hT : T.Finite := hf.subset fun _ h => h.1
  letI : Fintype T := hT.fintype
  have hex : ∀ P : T, ∃ a : C, a ∈ P.1 ∧ a ∉ q := by
    intro P
    apply IsConcreteLE.not_le_iff_exists.1
    exact fun h => P.2.2 (P.2.1.eq_of_le hq.ne_top h)
  let a : T → C := fun P => (hex P).choose
  have ha : ∀ P : T, a P ∈ P.1 ∧ a P ∉ q := fun P => (hex P).choose_spec
  refine ⟨∏ P : T, a P, ?_, ?_⟩
  · intro h
    obtain ⟨P, _, hP⟩ := (Ideal.IsPrime.prod_mem_iff).1 h
    exact (ha P).2 hP
  · intro P hP hPq
    let i : T := ⟨P, hP, hPq⟩
    obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
    rw [hb]
    exact P.mul_mem_right b (ha i).1

/-- Inverting a separator in a Dedekind domain inverts every element outside
the selected maximal ideal. -/
theorem separator_inverts_complement [IsDedekindDomain C]
    (q : Ideal C) [q.IsMaximal] (s : C) (hs : s ∉ q)
    (hsep : ∀ P : Ideal C, P.IsMaximal → P ≠ q → s ∈ P)
    (A : Type*) [CommRing A] [Algebra C A] [IsLocalization.Away s A] :
    ∀ t : C, t ∉ q → IsUnit (algebraMap C A t) := by
  intro t ht
  by_contra hunit
  obtain ⟨J, hJ, hle⟩ := (Ideal.span {algebraMap C A t}).exists_le_maximal
    (Ideal.span_singleton_ne_top hunit)
  letI := hJ
  let P := J.comap (algebraMap C A)
  have htP : t ∈ P := hle (Ideal.mem_span_singleton_self _)
  have hP0 : P ≠ ⊥ := by
    intro h0
    have ht0 : t = 0 := by simpa only [h0, Ideal.mem_bot] using htP
    exact ht (ht0 ▸ Ideal.zero_mem q)
  have hPprime : P.IsPrime := inferInstance
  have hPmax : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP0 hPprime
  have hPq : P ≠ q := fun h => ht (h ▸ htP)
  have hsP := hsep P hPmax hPq
  exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem J hsP (IsLocalization.Away.algebraMap_isUnit s))

/-- A prime localization of a semilocal Dedekind domain is a localization away
from one constructed element, hence is finitely presented. -/
theorem semilocal_prime_finitePresentation [IsDedekindDomain C]
    (hf : {P : Ideal C | P.IsMaximal}.Finite) (q : Ideal C) [q.IsMaximal]
    (B : Type*) [CommRing B] [Algebra C B] [IsLocalization.AtPrime B q] :
    Algebra.FinitePresentation C B := by
  obtain ⟨s, hs, hsep⟩ := exists_local_separator hf q
  haveI : IsLocalization.AtPrime (Localization.Away s) q :=
    IsLocalization.of_le (Submonoid.powers s) q.primeCompl
      (Submonoid.powers_le.2 hs)
      (separator_inverts_complement q s hs hsep (Localization.Away s))
  haveI : IsLocalization.Away s B := IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers s) (IsLocalization.algEquiv q.primeCompl (Localization.Away s) B)
  exact IsLocalization.Away.finitePresentation s

end FiniteExtensionValuation
