# height-glue results log

## AnalyticUniformizationUnique (AUUnique.lean)
- 07:10 AUUnique.lean part 1 compiles (VERIFIED): `anTop` (analytic topology on 𝒢.Pts τ),
  `continuous_of_isAnalyticUniformization`, `au_eq_iff`, `exists_linearEquiv_comp_eq`
  (two surjections V → W of fin-dim ℂ-spaces differ by an automorphism of V).
- Observation (VERIFIED by reading Models.lean): the kernel's `AnalyticUniformizationUnique` has NO
  lattice hypothesis on Λ, Λ'; it quantifies over degenerate uniformizations (g > dim A) too. It is
  still true (every analytic uniformization is exp ∘ (surjective linear map)); the proof plan factors
  every Φ through one full-lattice Φ₀.
- 07:30 AUUnique.lean compiles, no sorry (VERIFIED, `lake env lean`, ~70 s incl. import):
  `analyticUniformizationUnique_of (hE : ImmersiveUniformizationExists) (hT : AnalyticPointsT2) :
  AnalyticUniformizationUnique` — axioms [propext, Classical.choice, Quot.sound].
  Proved steps: Φ continuous for anTop; ℂ^{g₀}/Λ₀ compact (IsZLattice.isCompact_range_of_periodic);
  induced bijection a homeomorphism (compact → T2); covering lift (existsUnique_continuousMap_lifts);
  additivity (connectedness + discreteness); ℝ-linear (toRealLinearMap); ℂ-linear (immersion at 0 +
  chain rule over ℝ); surjective (Baire, countable Λ₀); T from exists_linearEquiv_comp_eq.
  Corollary `isImmersiveAtZero_of`: every full-lattice uniformization is immersive at 0.
  Leaves: `ImmersiveUniformizationExists` (Mumford AV §1 + analytic structure by regular functions;
  implies kernel AnalyticUniformizationExists, proved), `AnalyticPointsT2` (SGA1 XII 3.1 / GAGA).
