/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/Ideal.lean
Original SHA-256: 4fe9048fd70748a0335c5bcf32ec09f69859b70a52132d96f548eaf709c711f6
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/RingTheory/DedekindDomain/Ideal.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.Factorization
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

namespace Ideal

section CommSemiring

variable {R R' : Type*} [CommSemiring R] [CommSemiring R']

/- Divisibility of ideals is unchanged by pushing forward along a ring isomorphism: `Ideal.map e`
and `Ideal.map e.symm` are mutually inverse homomorphisms of the semirings of ideals. -/
theorem map_dvd_map_iff_of_ringEquiv (e : R ≃+* R') (I J : Ideal R) :
    Ideal.map e I ∣ Ideal.map e J ↔ I ∣ J := by
  -- `Ideal.map` sees `e` through `FunLike`, so `e` and its `RingHom` coercion give the same ideal;
  -- passing to the coercion is what lets `Ideal.mapHom` carry the divisibility.
  change Ideal.map (e : R →+* R') I ∣ Ideal.map (e : R →+* R') J ↔ I ∣ J
  refine ⟨fun h ↦ ?_, fun h ↦ by
    simpa only [mapHom_apply] using map_dvd (mapHom (e : R →+* R')) h⟩
  have hcomp : (e.symm : R' →+* R).comp (e : R →+* R') = RingHom.id R := by ext x; simp
  simpa only [mapHom_apply, Ideal.map_map, hcomp, Ideal.map_id] using
    map_dvd (mapHom (e.symm : R' →+* R)) h

/- The prime-power divisibility `p ^ n ∣ I` is unchanged by pushing forward along a ring
isomorphism. -/
theorem map_pow_dvd_map_iff_of_ringEquiv (e : R ≃+* R') (p I : Ideal R) (n : ℕ) :
    (Ideal.map e p) ^ n ∣ Ideal.map e I ↔ p ^ n ∣ I := by
  rw [← Ideal.map_pow]
  exact map_dvd_map_iff_of_ringEquiv e (p ^ n) I

end CommSemiring

section RingEquivDedekind

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

/- Multiplicities in the factorisation of an ideal are unchanged by pushing forward along a ring
isomorphism: the number of times `Ideal.map e p` divides `Ideal.map e I` is the number of times
`p` divides `I`. -/
theorem count_factors_map_of_ringEquiv (e : R ≃+* R') {p I : Ideal R} (hp : Prime p) (hI : I ≠ ⊥) :
    (Associates.mk (Ideal.map e p)).count (Associates.mk (Ideal.map e I)).factors =
      (Associates.mk p).count (Associates.mk I).factors := by
  classical
  have hpb : p ≠ ⊥ := by simpa only [zero_eq_bot] using hp.ne_zero
  have hpmapb : Ideal.map e p ≠ ⊥ := by
    simpa only [ne_eq, map_eq_bot_iff_of_injective e.injective] using hpb
  have hI0 : I ≠ 0 := by simpa only [zero_eq_bot] using hI
  -- `map_isPrime_of_equiv` is an instance, so it fires once `p.IsPrime` is in the context.
  have : p.IsPrime := (prime_iff_isPrime hpb).mp hp
  have hpmap : Prime (Ideal.map e p) := (prime_iff_isPrime hpmapb).mpr (map_isPrime_of_equiv e)
  have hmkImap : Associates.mk (Ideal.map e I) ≠ 0 := Associates.mk_ne_zero.mpr
    (by simpa only [ne_eq, zero_eq_bot, map_eq_bot_iff_of_injective e.injective] using hI)
  have hmkI : Associates.mk I ≠ 0 := Associates.mk_ne_zero.mpr hI0
  -- Both counts are pinned by the same `n ≤ ·` characterisation, through `prime_pow_dvd_iff_le`.
  have key : ∀ n : ℕ, n ≤ (Associates.mk (Ideal.map e p)).count
        (Associates.mk (Ideal.map e I)).factors ↔
      n ≤ (Associates.mk p).count (Associates.mk I).factors := fun n ↦ by
    rw [← Associates.prime_pow_dvd_iff_le hmkImap (Associates.irreducible_mk.mpr hpmap.irreducible),
      ← Associates.prime_pow_dvd_iff_le hmkI (Associates.irreducible_mk.mpr hp.irreducible),
      ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
      Associates.mk_le_mk_iff_dvd]
    exact map_pow_dvd_map_iff_of_ringEquiv e p I n
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

end RingEquivDedekind

section Multiplicity

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

/- **Distinct nonzero primes have zero multiplicity in one another.** In a Dedekind domain a
nonzero prime is maximal, so `Q ∣ P` would force `Q = P`.

This is the coefficient-level form of "a prime power is supported at one prime": in a weighted
sum over the primes above a fixed ideal, every term but the matching one vanishes. -/
end Multiplicity

section Injective

/- If the contraction of `J` along an injective ring homomorphism is nonzero, so is `J` itself.

This is the eliminator that discharges the nonvanishing hypothesis of
`IsDedekindDomain.HeightOneSpectrum.comapOfNeBot` when a prime is contracted through an
intermediate ring: contract all the way down to a base where nonvanishing is already known, and
read the intermediate step off from that. Only injectivity of the *lower* map is needed; the map
producing `J` plays no role, so it does not appear. -/
end Injective

end Ideal

namespace IsDedekindDomain.HeightOneSpectrum

section Comap

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]

/- The height-one prime of `B` obtained by contracting a height-one prime of `C` along a ring
homomorphism `ψ : B →+* C`, given that the contraction is nonzero.

Mathlib's `IsDedekindDomain.HeightOneSpectrum.comap` is the same construction, but it asks for `ψ`
to be **surjective** and derives the `ne_bot` field from that. `comapOfNeBot` **generalises** it:
the surjective case is recovered by supplying `(Ideal.eq_bot_of_comap_eq_bot' hf).mt w.ne_bot`, and
only the converse fails.

The generality is needed because the maps contracted along here are embeddings into completions —
`R → v.adicCompletionIntegers K` — which are neither surjective, so Mathlib's `comap` does not
apply, nor integral `Algebra` maps, so `HeightOneSpectrum.under` does not either. (`ℤ → ℤ_p` is
flat, not integral.) The `ne_bot` hypothesis has to be supplied by hand.

Adapted from Michael Stoll's `EllipticCurves` (`EllipticCurves/Mathlib/Basic.lean` line 539, Apache
2.0, at the roadmap's pin `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`); the `ne_bot`-as-hypothesis
formulation is the source's. -/
end Comap

section RingEquivTransport

variable {R R' : Type*} [CommRing R] [CommRing R']

/- Mathlib's transport `equivOfRingEquiv e` of height one primes along a ring isomorphism `e`
pushes the underlying ideal forward: `(equivOfRingEquiv e v).asIdeal = Ideal.map e v.asIdeal`. -/
end RingEquivTransport

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/- Distinct height one primes are incomparable: a height one prime is not contained in any
other one, since both are maximal. -/
end IsDedekindDomain.HeightOneSpectrum

namespace Ideal

-- `_root_` disambiguates: inside `namespace Ideal`, a bare `open IsDedekindDomain` would resolve
-- to the `Ideal.IsDedekindDomain` namespace of Mathlib's ramification indices, which the
-- `Factorization` import above makes visible here.
open _root_.IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/- An ideal of a Dedekind domain is **prime to** a set `S` of height-one primes when it is
nonzero and no prime of `S` divides it. Nonzeroness is part of the definition, so `⊥` is prime
to no set at all — not even to `∅`. -/
variable {I J : Ideal R} {S T : Set (HeightOneSpectrum R)}

end Ideal

section DiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum

/- The maximal ideal is the only height-one prime of a discrete valuation ring.

Mathlib has `IsDiscreteValuationRing.maximalIdeal` as a `HeightOneSpectrum` and
`IsLocalRing.eq_maximalIdeal` for ideals, but not that the two agree at the level of
`HeightOneSpectrum`. That identification is what lets a statement about the height-one primes of a
discrete valuation ring be read as a statement about its valuation. -/
-- Not `@[simp]`: the left-hand side is the bare variable `P`, so its head symbol is a variable and
-- the compiler rejects the annotation outright ("the theorem will be tried on every simp step").
end IsDedekindDomain.HeightOneSpectrum

end DiscreteValuationRing

end
