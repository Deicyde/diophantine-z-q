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
- Bridge.lean merged into G4.lean (scratch files cannot import each other); Bridge.lean removed.

## G4.lean — core COMPILED (lake env lean, no errors, no sorry)
- `G4WeilRes.toGL`, `toGL_injective`: `(M ≃ₗ[ℤ] M) →* GL_r(ℤ)` from a basis, injective.
- `G4WeilRes.homField_core`: K ⊆ ℚ̄ finite Galois, GalUnramifiedOutside K T; ρ : G_ℚ →* (M ≃ₗ[ℤ] M), M with
  basis `Fin r`, open stabilizers, inertia over p ∉ T acting trivially ⇒ ∃ L ⊇ K finite Galois,
  G_L acts trivially on M, finrank L ≤ finrank K · 3^(r²), GalUnramifiedOutside L T, ∀ p ∉ T UnramifiedAt L p.
  Uses GlueRepo.TorsionFree.card_le_three_pow (Minkowski), InfiniteGalois.*, the bridge.
- `G4WeilRes.homField_le_heightD`: with finrank K ≤ heightF0, r ≤ 16·heightF0² ⇒ finrank L ≤ heightD
  (GlueRepo.Numerics.a8_degree, ZInQ.Compiler.Precision.heightD_eq).
