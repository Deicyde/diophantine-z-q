# height-glue results log

## AnalyticUniformizationUnique (AUUnique.lean)
- 07:10 AUUnique.lean part 1 compiles (VERIFIED): `anTop` (analytic topology on 𝒢.Pts τ),
  `continuous_of_isAnalyticUniformization`, `au_eq_iff`, `exists_linearEquiv_comp_eq`
  (two surjections V → W of fin-dim ℂ-spaces differ by an automorphism of V).
- Observation (VERIFIED by reading Models.lean): the kernel's `AnalyticUniformizationUnique` has NO
  lattice hypothesis on Λ, Λ'; it quantifies over degenerate uniformizations (g > dim A) too. It is
  still true (every analytic uniformization is exp ∘ (surjective linear map)); the proof plan factors
  every Φ through one full-lattice Φ₀.
