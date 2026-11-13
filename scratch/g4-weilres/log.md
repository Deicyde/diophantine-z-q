# g4-weilres results log

## Setup
- Built `ZInQKernel.HDecomp.B3Unram.B3b`, `ZInQKernel.HDecomp.Repo.TorsionFree` (lake build, OK).
- Consumer of G4 (VERIFIED by reading): `GlueDescent.B3Q.b3_degree_le_QM` (ZInQKernel/HDecomp/Descent/B3Assembly.lean)
  takes `L : IntermediateField ℚ ℚ̄`, `[FiniteDimensional ℚ L] [IsGalois ℚ L]`, `finrank ℚ L ≤ heightD`,
  `∀ p : Nat.Primes, p ∉ ramSet S u → UnramifiedAt L p`, and `ε` with `InflatedFrom L ε`.
  `GlueAssembly.CMOutput` takes only a real `d` with `1 ≤ d ≤ heightD`.

## Bridge.lean — COMPILED (lake env lean, no errors, no sorry)
- `G4WeilRes.exists_liesOver`: a valuation subring of ℚ̄ over every prime p.
- `G4WeilRes.exists_inertia_restrict`: L finite Galois, σ trivial mod w on integers of L ⇒ ∃ s ∈ I_w, s = σ on L.
- `G4WeilRes.unramifiedAt_of_inertia_le`: (∀ w over p, I_w ≤ G_L) ⇒ `UnramifiedAt L p`.
- `G4WeilRes.galUnramifiedOutside_iff`: `GalUnramifiedOutside L T ↔ ∀ p ∉ T, UnramifiedAt L p` (finite Galois L).
