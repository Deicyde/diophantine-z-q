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
- HeightGlue.lean (assembled by build.py: base/Kernel_metrization2.lean = scratch/metrization2/Kernel.lean
  verbatim; base/JacDescends_unifdims.lean = unif-dims Combined.lean l.1615-1752, 1907-1933, 1937-2190
  minus duplicates; AUUnique.lean; part_main.lean) compiles, exit 0 (VERIFIED):
  * `analyticPointsT2 : AnalyticPointsT2` — PROVED, no hypotheses (productMapLocalStructure on the
    division morphism x·y⁻¹ + pts_eq_of_evalAt).
  * `isImmersiveAtZero_of_discrete` — PROVED: every analytic uniformization with discrete kernel is
    immersive at 0 (metrization2's steps 2-5).
  * `analyticUniformizationUnique_of_exists (hE : AnalyticUniformizationExists) :
    AnalyticUniformizationUnique` and `analyticUniformizationUnique_of_t35 (hT35 :
    LeafPush2.UniformizationExists)`. Axioms standard.
  => AN3U is a consequence of the kernel's AN3 existence Prop (and of T35); the two leaves of
  AUUnique.lean are no longer needed.
