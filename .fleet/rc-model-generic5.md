# rc-model-generic5

**Retired frozen fields: none yet.** The hRC GLUE row (docs/one-proof/OPEN.md, section hRC: docs/one-proof/OPEN.md#hrc) and PreLeaves.odd_staged (RC/Wiring/Leaves.lean:305) are unchanged. GoodRow is the input G of oddStagedOfGoodRows (RC/PMWire/Assembly.lean:120, :220); supplying its fields retires nothing by itself.

**No error verdict.** No leaf was added or proposed.

**Main result.** GoodRow.extension (RC/PMWire/Model.lean:59) is proved at the pinned model: `ModelGeneric5.goodRow_extension h₅ htame h₂`. The witness is `Wint`, which is Spec of the restriction of the actual rational Atkin–Lehner ring map to Pinned.Y0LevelAlgebra. That restriction exists by integral closure over R[j] (Φ_Q monic; A_R/ℓ reduced; A_R flat). ExtendsAtkin is a theorem (`extendsAtkin_Wint`), not a definition. Wint is the unique extension (`eq_Wint_of_extendsAtkin`) and an involution (`Wint_comp_self`).

**Stage primes.** For every StageKummer.Setup s and every stage i:
- `stagePrime_five_le` gives h₅.
- `stagePrime_not_dvd_tame` gives htame, given (N φ(N)).primeFactors ⊆ s.B. The GoodRow wiring must choose B accordingly.
- `two_le_level` gives h₂ from the existing hypothesis hN : 0 < level of oddStagedOfGoodRows, with no leaf.

**Item 3: scoped stop.** At every complex point, atkinRat acts on pinned classes as τ ↦ W_Q τ (`rationalPoints_atkinRat_complex`). Open, restated: (item 3, characteristic 0, choice-free) for every algebraically closed k of characteristic 0, every x, every pair (E, C) representing rationalPoints x and every seam g of E.cyclicQuotientCurve C_Q Q with g.ker = C_Q, rationalPoints (x.comp (atkinRatAlg h₂ hQ)) is the class of (E.cyclicQuotientCurve C_Q Q, g(E[Q] + C)); continued in rc-model-generic6. **Item 4** (characteristic ℓ, existential over separable seams): for every x into an algebraically closed k of characteristic ℓ and every pair (E, C) representing Y0LevelPoints x, there is a separable seam g (finrankAlong k ι = Q) with g.ker = C_Q and Y0LevelPoints (x.comp atkinLevelAlg) the class of (E.cyclicQuotientCurve C_Q Q, g(E[Q] + C)); continued in rc-model-generic6. Its consumer also needs uniqueness of separable quotients in characteristic ℓ (Silverman III.4.11–4.12, UNVERIFIED). point_W is not supplied; it also needs `point` from the hCM lane. **Item 5** is done (docs/research/rc-model-generic4.md).

**What compiles.** Six Lean modules under ZInQKernel/Contrib/OneProof/RC/ModelGeneric5/: StagePrimes, AtkinField, IntegralTransfer, RationalChart, Extension and ComplexPoints. Each builds with lake build, with no sorry and no axiom declaration. Every #print axioms lists only propext, Classical.choice and Quot.sound, or a subset. The report is docs/research/rc-model-generic5.md.

**What remains.** Items 3, 4 and point_W, with their reductions, are in the report's table. Relations needs a HeckePacket and a HeckeIdentity: a correspondence model (model lane), lifts through point (hCM lane), the coarse-fibre divisor (adelic side) and the generic Hecke identity (generic4 item 4, open).

Work tip (all modules and the report): 2a7d5c71edd5fbb66aa1a6f0e9485f21d66cdf2f. This file is committed on top of it.
