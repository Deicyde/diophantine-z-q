/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/PrimesAbove.lean
Original SHA-256: 8e68feb049c2133d53b321e81d4ea913381055cd29eb559b3d3c4f77aa19797a
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
TauCeti/RingTheory/DedekindDomain/PrimesAbove.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

namespace IsDedekindDomain

variable (R : Type*) [CommRing R] (B : Type*) [CommRing B] [Algebra R B]

namespace HeightOneSpectrum

section IsDomain

variable [IsDomain R] [IsDomain B] [Algebra.IsIntegral R B]

/- A height one prime of `B` lies over its own contraction to `R`.

Mathlib's `Ideal.over_under` is this statement for `Ideal.under`, but instance search does not see
through the `HeightOneSpectrum.asIdeal` projection to reach it, so it is registered here. Results
stated at `under R w` and consuming a `LiesOver` hypothesis, such as
`HeightOneSpectrum.valuation_liesOver`, do not fire without it. -/
instance liesOver_under (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (under R w).asIdeal :=
  ⟨rfl⟩

/- The primes of `B` lying above a set `S` of primes of `R`: the preimage of `S` under the
contraction `HeightOneSpectrum.under R`. -/
end IsDomain

section

variable {R B}

variable (B) [FaithfulSMul R B]

/- Only finitely many nonzero primes of a Dedekind domain `B` lie over a given nonzero
prime of `R`. The extension need not be integral, and `R` need not be Dedekind. -/
instance finite_liesOver [IsDedekindDomain B] (v : HeightOneSpectrum R) :
    Finite {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} := by
  have h := Ideal.finite_factors (Ideal.map_ne_bot_of_ne_bot (S := B) v.ne_bot)
  exact (h.subset fun w hw ↦ Ideal.dvd_iff_le.mpr
    (Ideal.map_le_iff_le_comap.mpr (le_of_eq hw.over))).to_subtype

end

/- Only finitely many primes of `B` lie above a finite set of primes of `R`. -/
end HeightOneSpectrum

variable [IsDomain R] [IsDedekindDomain B] [Algebra.IsIntegral R B]

/- The `S`-Selmer group of `L`, where `B` is a Dedekind domain with fraction field `L` and `S`
is a set of primes of `R`: the classes of `Lˣ` modulo `n`-th powers whose valuation is divisible
by `n` at every prime of `B` not lying above `S`. -/
end IsDedekindDomain

end
