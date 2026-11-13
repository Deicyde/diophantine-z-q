# height-bc (wave 27): `HodgeLineBaseChange` and H4a `ModelHeightBaseChange`

**Result.** Both Props are proved, with their statements unchanged, from **four smaller named glue
statements** (VERIFIED: `scratch/height-bc/Final.lean`, 0 errors, no `sorry`, 28 `#print axioms`
all `[propext, Classical.choice, Quot.sound]`). The theorems are `modelHeightBaseChange_of_glue4`
and `hodgeLineBaseChange_of_glue4`. The four are glue, not leaves, and are stated over a natural
map built in Lean for a base change `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}`:
- `π`: the projection `𝒢' → 𝒢`;
- `bcMap`: its stalk map at the origin;
- `ψ`: the induced map `L' ⊗ ⋀^g π^*` on Hodge spaces;
- `β`: the map on complex points.

The four glue statements:
- `HodgeBCInjective`: `ψ` is injective, and the Hodge spaces are lines simultaneously.
- `CotangentSpanBC`: the classes `π^*ω_{A_L}` span `ω_{A_{L'}}` over `𝓞_{L'}`.
- `OmegaBaseChange`: `ω_{𝒢'} ⊆ 𝓞_{L'}·π^*ω_𝒢`. The other inclusion is proved.
- `UniformizationLiftAnalytic`: regular functions on opens of `𝒢'` that are defined over `L'` are
  holomorphic along `Φ'` when `β∘Φ'` is a uniformization.

All four concern the local structure (stalks, affine opens) of the fibre product. Two read-only
model reviews found all of them true as written and none vacuous; there was no human review. The
descent half `h(𝒢) ≤ h(𝒢')` needs only the first and third (`modelHeightBaseChangeGE_of_main`).

**Proved along the way:**
- the Arakelov descent: choose the place above `σ` that maximizes the archimedean term; a finite
  index descends;
- `β` is a bijective homomorphism (`ptsBaseChangeBij`, `ptsBaseChangeMul`);
- uniformizations descend along `β`, and Jacobians are compatible (`jacDet_bcPts`);
- `ψ(⋀^g ω_𝒢) ⊆ ⋀^g ω_{𝒢'}`;
- the analytic input `GermDerivation`: the differential of `germAlong Φ` at `0` descends to a
  semilinear map on `𝔪/𝔪²`. This needed germs along `Φ` to be a ring homomorphism near `0`,
  `𝔪_ξ`-germs to vanish at the unit point, and structure sections to have the value `τ(r)`.

**Finding.** `HodgeLineBaseChange` alone gives only `h(𝒢') ≤ h(𝒢)`. The other inequality needs a
converse line clause and descent of uniformizations (`HodgeLineBaseChangeDescent`). Both are now
supplied.

**Integration (VERIFIED):**
- `H5WithBC.lean`: h5-glue's H5 from N1, N2 and the four glue statements
  (`stableFaltingsHeight_eq_neron_of_glue4`).
- `G0WithBC.lean`: g0-split's piece `StableHeightBaseChange` from the four glue statements
  (`stableHeightBaseChange_of_glue4`). g0-stablebc's `Main.part` compiles verbatim over the
  kernel's objects, given one alias.

**What remains.** The four glue statements, which are STANDARD algebraic geometry and not proved in
Lean. A Mathlib-style lemma on stalks of fibre products is the natural common first step. Report:
`docs/research/height-bc.md`; log: `scratch/height-bc/log.md`.
