import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.DedekindDomain.Basic

/-! # Closed exceptional points of the original good-reduction neighborhood -/

set_option autoImplicit false

namespace ZInQ.Contrib.IsogenyDegree

/-- Over a noetherian domain of dimension at most one, the complement of a basic
open defined by a nonzero element is a finite set of closed points. For a model over
`𝓞 L`, this converts a fixed good-reduction basic open into the finite exception set
for the fiberwise identity component, without changing the model or its base. -/
theorem basicOpen_compl_finite_closed {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.DimensionLEOne R] {f : R} (hf : f ≠ 0) :
    (↑(PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum R))ᶜ.Finite ∧
      ∀ t ∉ PrimeSpectrum.basicOpen f, IsClosed ({t} : Set (PrimeSpectrum R)) := by
  classical
  have hmax {t : PrimeSpectrum R} (ht : t ∉ PrimeSpectrum.basicOpen f) :
      t.asIdeal.IsMaximal := by
    have hft : f ∈ t.asIdeal := by simpa [PrimeSpectrum.mem_basicOpen] using ht
    exact Ring.DimensionLEOne.maximalOfPrime (fun h => hf (by simpa [h] using hft)) t.isPrime
  refine ⟨?_, fun _ ht => (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (hmax ht)⟩
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {f})).preimage
    (fun a _ b _ h => PrimeSpectrum.ext h)).subset ?_
  intro t ht
  have hft : f ∈ t.asIdeal := by
    simpa [Set.mem_compl_iff, PrimeSpectrum.mem_basicOpen] using ht
  refine ⟨⟨t.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hft⟩, fun q hq hqt => ?_⟩
  have hq0 : q ≠ ⊥ := fun h => hf (by
    have := hq.2 (Ideal.mem_span_singleton_self f)
    simpa [h] using this)
  have hqm : q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hq0 hq.1
  exact (hqm.eq_of_le (hmax ht).ne_top hqt).ge

/-- A nonempty open of this spectrum contains a basic open with finite closed complement.
This is the exact output shape needed after spreading out connected fibers on an open. -/
theorem exists_basicOpen_with_finite_closed_exception {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.DimensionLEOne R] {U : Set (PrimeSpectrum R)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ f : R, f ≠ 0 ∧ (↑(PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum R)) ⊆ U ∧
      (↑(PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum R))ᶜ.Finite ∧
      ∀ t ∉ PrimeSpectrum.basicOpen f, IsClosed ({t} : Set (PrimeSpectrum R)) := by
  classical
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff U).mp hU
  obtain ⟨t, ht⟩ := hne
  have ht' : ¬ s ⊆ (t.asIdeal : Set R) := by
    intro h
    have htV : t ∈ PrimeSpectrum.zeroLocus s := h
    rw [← hs] at htV
    exact htV ht
  obtain ⟨f, hfs, hfnot⟩ := Set.not_subset.mp ht'
  have hf : f ≠ 0 := fun e => hfnot (e.symm ▸ t.asIdeal.zero_mem)
  refine ⟨f, hf, ?_, basicOpen_compl_finite_closed hf⟩
  intro z hz
  by_contra hzu
  have hzV : z ∈ PrimeSpectrum.zeroLocus s := hs ▸ hzu
  exact (PrimeSpectrum.mem_basicOpen f z).mp hz (hzV hfs)

#print axioms basicOpen_compl_finite_closed
#print axioms exists_basicOpen_with_finite_closed_exception

end ZInQ.Contrib.IsogenyDegree
