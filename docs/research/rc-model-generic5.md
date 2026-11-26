# The integral Atkin–Lehner operator on the pinned model, and the stage-prime hypotheses

**Retired frozen fields: none yet.** No field of the frozen target and no count changes. The hRC GLUE row (`docs/one-proof/OPEN.md`, section hRC: `docs/one-proof/OPEN.md#hrc`) and its odd-side input `PreLeaves.odd_staged` (`ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean:305`) are unchanged. `PMWire.GoodRow` is the input `G` of `oddStagedOfGoodRows` (`RC/PMWire/Assembly.lean:120`, theorem at `:220`). Supplying one of its fields retires no frozen field by itself.

**No error verdict.** No false manuscript claim, failed computation or misread citation was found. No leaf was added or proposed.

**Main result (item 2, complete).** `GoodRow.extension` (`RC/PMWire/Model.lean:59`) is proved at the pinned model, for every prime `q` with `0 < N.factorization q`: `ModelGeneric5.goodRow_extension` (`Extension.lean`). The witness is the named morphism `Wint h₅ htame h₂ hQ : Pinned.Y0Level h₅ htame h₂ ⟶ Pinned.Y0Level h₅ htame h₂`, which is `Spec` of the restriction of the actual rational Atkin–Lehner ring map to the integral ring. `ExtendsAtkin` is a theorem (`extendsAtkin_Wint`), not a definition. `Wint` is the only extension (`eq_Wint_of_extendsAtkin`) and is an involution (`Wint_comp_self`).

**Item 1, complete.** At every stage prime `p = (s.q.stage i).p` of a `StageKummer.Setup s`:
- `h₅` holds: `stagePrime_five_le`.
- `htame` holds whenever the Setup's exclusion set contains the primes of `N φ(N)`: `stagePrime_not_dvd_tame`.
- `h₂ : 2 ≤ StageKummer.level ℓ` follows from the existing hypothesis `hN : 0 < StageKummer.level ℓ` of `oddStagedOfGoodRows`: `two_le_level`. This needs no leaf.

**Item 3: scoped stop.** At every complex point, the action of `atkinRat` on pinned classes is proved to be the matrix translate τ ↦ W_Q τ (`rationalPoints_atkinRat_complex`). The moduli form (E, C) ↦ (E/C_Q, (E[Q]+C)/C_Q) is open; it is stated below.

**Item 4: not started.** It depends on item 3.

**Item 5: done**, in one commit to `docs/research/rc-model-generic4.md`.

All 6 new Lean modules (StagePrimes, AtkinField, IntegralTransfer, RationalChart, Extension, ComplexPoints) are under `ZInQKernel/Contrib/OneProof/RC/ModelGeneric5/`. Each builds with `lake build`, with no `sorry` and no axiom declaration. Every `#print axioms` gives a subset of `propext`, `Classical.choice`, `Quot.sound`.

## What each result discharges

| Result | Discharges |
| --- | --- |
| `goodRow_extension h₅ htame h₂` | field `extension` of `PMWire.GoodRow` for `M := Pinned.Y0Level h₅ htame h₂`, `source := ModelNeron.source h₅ htame h₂`. Instantiated at each stage prime, it supplies the `extension` field of every `G i` in `oddStagedOfGoodRows`. |
| `eq_Wint_of_extendsAtkin` | identifies `GoodRow.W` (`Model.lean:95`, the `choose` of `extension`) with `Wint` for any GoodRow built on the pinned model and source. This is what `point_W` will be read against. |
| `stagePrime_five_le s i` | hypothesis `h₅ : 5 ≤ ell` of `ModelNeron.source` / `Pinned.Y0Level` at `ell := (s.q.stage i).p`. |
| `stagePrime_not_dvd_tame s hN hB i` | hypothesis `htame : ¬ ell ∣ N * N.totient` at the same `ell`, for `N := StageKummer.level ℓ`, given `hB : (N * N.totient).primeFactors ⊆ s.B`. The future GoodRow wiring must build the Setup with this `B`. For `exists_detector_stages` sequences (over `stageExclusions ℓ Dw hstar B`) use `not_dvd_tame_of_not_mem_stageExclusions`. |
| `two_le_level hN` | hypothesis `h₂ : 2 ≤ N` of `ModelNeron.source` at `N := StageKummer.level ℓ`, from `hN : 0 < StageKummer.level ℓ` (`Assembly.lean:114`). |
| `Fact ell.Prime` | `⟨(s.q.stage i).prime⟩` (existing). |

None of these is a hypothesis of `oddStagedOfGoodRows` itself. They are the inputs needed to instantiate the pinned model at each stage prime, and the `extension` field of each `G i`.

## New definitions and theorems

`StagePrimes.lean` (item 1)
- `EcurveZ_disc : (EcurveZ l).Δ = 2304 * l ^ 6`.
- `stagePrime_not_dvd_disc s i`: `¬ (p : ℤ) ∣ Δ(EcurveZ ℓ)`. This is `StageKummer.stageGood` applied to the Setup's own sequence.
- `stagePrime_five_le s i : 5 ≤ p`. The prime satisfies `p ≡ 3 mod 4` (`stage_mod_four`), `3 ∣ 2304`, and `p ∤ Δ`.
- `stagePrime_not_dvd_tame s hN hB i`; `subset_stageExclusions`; `not_dvd_tame_of_not_mem_stageExclusions`.
- `two_le_newformLevel (hN : 0 < CST.newformLevel E) : 2 ≤ CST.newformLevel E`. At level one the cusp form vanishes: Mathlib's `CuspForm.rank_eq_zero_of_weight_lt_twelve` with `Γ₀(1) = SL₂(ℤ)`. But `a₁(E) = 1` (`NewformGlueG0.lFunction_one`). Then `two_le_level`.

`AtkinField.lean`
- `pullback_jq hQ : AtkinRational.pullback hQ j = j_Q` in `modularFunctionField N`. This holds because `j(W_Q τ) = j(Qτ)` (`AtkinRational.chart_coordinates`).
- `modularPolynomial_eval_field`: `Φ_M(j_M, j) = 0` in `modularFunctionField N` for `M ∣ N`. This is the vendored Laurent identity transported into the field.

`IntegralTransfer.lean` (pure commutative algebra)
- `isIntegral_of_finite`: integrality transfers along a finite map.
- `mem_range_of_isIntegral` and `exists_eq_of_isIntegralElem`. Suppose `πA` is radical and `κ π` is a unit. If `b` is integral over `A` and `πⁿ b ∈ κ(A)`, then `b ∈ κ(A)`.
- `isRadical_span_of_residue_reduced`: if `k ⊗_R A` is reduced and `𝔪_R = (π)`, then `πA` is radical.
- `restrictRange`, `restrictRange_spec`: the restriction of a ring endomorphism to a subring it preserves.

`RationalChart.lean` (item 2(a)–(c) on the generic fibre)
- `ratToField h₂ : Y0RationalAlgebra h₂ →+* modularFunctionField N`. This is the actual comparison inside `ModelNeron.chartField`. Supporting results: `ratToField_J` (j ↦ jq) and `ratToField_isFractionRing`.
- `isIntegral_jqN`; `isIntegral_pullback_ratToField`.
- `atkinRat h₂ hQ`, a ring endomorphism of the pinned rational ring, with `ratToField_atkinRat : ratToField (atkinRat a) = pullback hQ (ratToField a)`. The ring is integrally closed (the private `rationalAlgebra_isIntegrallyClosed`, `RC/ModelGeneric2/AffineComparison.lean:29`, opened at `RC/ModelGeneric5/RationalChart.lean:37` and used at `:142`), finite over `ℚ[j]` (`Y0RationalJMap_finite`), and `pullback hQ` moves `j` to the root `j_Q` of the monic `Φ_Q(X, j)`.
- `genericMap_eq_chart`: the generic point of the pinned rational open is the generic point of the fixed curve.
- `atkinRat_openImmersion : Spec(atkinRat) ≫ rationalOpenImmersion = rationalOpenImmersion ≫ (rationalAtkin hQ).hom`. The two sides are compared at the generic point (`exists_modelMap`); the source is reduced and the target separated. This is item 2(a): W_Q preserves the finite chart.

`Extension.lean` (item 2(b)–(e))
- `levelToRat`: the generic-fibre map `A_R → ℚ ⊗_R A_R ≃ A_ℚ` (`Y0RationalBaseChange`). `levelToRat_injective` follows from flatness (`levelQuotient_flat`). `exists_pow_mul_mem_range`: every element times a power of ℓ comes from `A_R`.
- `isRadical_span_ell`: `ℓA_R` is radical, because the special fibre is reduced (`levelQuotient_fibre_reduced` at the residue field).
- `isIntegral_atkinRat_levelToRat`; `atkinLevel hQ` (the restriction) with `levelToRat_atkinLevel`; `atkinLevel_algebraMap`.
- `Wint h₅ htame h₂ hQ := Over.homMk (Spec.map atkinLevel)`.
- `genericIso_inv_fst`; `conj_of_pullback`; `generic_map_Wint`, the generic fibre of `Wint` conjugated to `Spec(atkinRat)`.
- `extendsAtkin_Wint q`, `goodRow_extension`, `eq_Wint_of_extendsAtkin`.

`ComplexPoints.lean` (item 3, analytic half)
- `atkinRat_involutive`, `atkinLevel_involutive`, `Wint_comp_self`.
- `rationalPointAtParameter_atkinRat hQ τ`: `x_τ ∘ atkinRat = x_{W_Q τ}`.
- `rationalPoints_atkinRat_complex hQ y`: for every complex point `y` there is τ with `rationalPoints y = analyticCyclicPair τ` and `rationalPoints (y ∘ atkinRat) = analyticCyclicPair (W_Q τ)`. Both readings are actual.

On normality (item 2(b)): the run does not need normality of the integral ring, which is in neither Mathlib nor the tree. It uses only that `A_R` is integrally closed in `A_R[1/ℓ] = A_ℚ`. This follows elementarily from flatness and the reducedness of `A_R/ℓA_R` (`mem_range_of_isIntegral`).

## `PMWire.GoodRow` per-field table (`RC/PMWire/Model.lean:35`)

| Field | Status | Supplier / owner lane |
| --- | --- | --- |
| `closed` | supplied upstream | `ModelNeron.closed` |
| `M`, `smoothM`, `reducedM`, `separatedM`, `denseGeneric` | supplied upstream | `Pinned.Y0Level`, `Y0Level_smooth`, `ModelNeron.reducedM`/`separatedM`/`denseGeneric` |
| `source` | supplied upstream | `ModelNeron.source` |
| `E`, `groupE`, `neron`, `jE`, `properGenericE`, `geomIntGenericE` | supplied upstream | rc-model-neron (local Néron target) |
| `readComplex`, `readComplex_eq` | open | target lane (rc-model-target) |
| `point` | open | same-place comparison (hCM lane) |
| **`extension`** | **supplied (this run)** | `ModelGeneric5.goodRow_extension` |
| `point_W` | open | input of `SamePlaceData`, owned by the same-place lane (the hCM lane); also needs the special-fibre action of `Wint` (item 4 here, not started) |
| `read`, `read_frob` | open | target lane |
| `point_frob`, `frobenius_sq` | open | same-place comparison (hCM lane) |

Pinned-model parameters at each stage: `h₅`, `htame` (given `B`) and `h₂` (given `hN`) are supplied by this run. `htame` is owned by the GoodRow wiring for the choice of `B`.

## What remains

| Item | Smallest faithful open statement | Reduces to |
| --- | --- | --- |
| 3 (char. 0), choice-free | For every algebraically closed `k` of characteristic 0, every prime `q` with `0 < N.factorization q`, `Q = q^(v_q N)` with `hQ := TauCeti.Nat.isExactDivisor_primePow`, every `x : Y0RationalAlgebra h₂ →ₐ[ℚ] k`, every pair `(E, C)` representing `rationalPoints h₂ x` (`E` elliptic over `k`, `C` cyclic of order `N`), and every seam `g : E.toAffine.Point →+ (E.cyclicQuotientCurve C_Q Q).toAffine.Point` (there are `ι`, `hι` with `FiniteAlong k ι` and `IsSeam ι hι g`, as `ModelGeneric4.exists_quotientSeam` produces) with `g.ker = C_Q`, where `C_Q = (N/Q) • C`: `rationalPoints h₂ (x.comp (atkinRatAlg h₂ hQ))` is the class of `(E.cyclicQuotientCurve C_Q Q, g(E[Q] + C))`. Independence of `g` and of the representative is a corollary (the left side involves no choice). Pieces: (a) `g(E[Q] + C)` is cyclic of order `N` for every group homomorphism `g` with `g.ker = C_Q`, over every algebraically closed `k` with `N` invertible; (b) the complex step, `analyticCyclicPair τ ↦ analyticCyclicPair (W_Q τ)`; (c) transfer from `ℂ` to every algebraically closed `k` of characteristic 0. Continued in rc-model-generic6. | (a): `card_torsionBy_eq_sq_of_isAlgClosed` for every `d ∣ Q` with `AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq`, then finite group theory. (b): the lift of a seam to `z ↦ αz` (from the proof of `ModelGeneric4.j_eq_analyticJN_of_seam`, which needs a point formula for the function-field isomorphism of a Weierstrass variable change), `PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker`, and the Atkin–Lehner lattice identity through `ModelGeneric4.analyticCyclicPair_eq_of_scale`; background Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., 2009, VI.3.6, VI.4.1 (UNVERIFIED); Diamond–Shurman 2005 §1.5 (UNVERIFIED). (c): `rationalPoints`, the Vélu composite and seams commute with field embeddings; descent to a subfield embeddable in `ℂ`. Uniqueness of quotients is not needed. The moduli form is **ON THE SPOT (c)**: Ogg 1974 defines w_M analytically; Conrad 2007 has only quotient maps. |
| 4 (char. ℓ), existential over separable seams | For every algebraically closed `k` of characteristic ℓ with `Algebra (LocalIntegers ell) k`, every `x : Y0LevelAlgebra h₅ htame h₂ →ₐ[LocalIntegers ell] k` and every pair `(E, C)` representing `Y0LevelPoints x`, there is a separable seam `g` (a characteristic-free `IsSeam ι hι g` with `FiniteAlong k ι` and `finrankAlong k ι = Q`) with `g.ker = C_Q` and `Y0LevelPoints (x.comp atkinLevelAlg)` equal to the class of `(E.cyclicQuotientCurve C_Q Q, g(E[Q] + C))`. Continued in rc-model-generic6. | A characteristic-free copy of the seam construction (the tree's `IsSeam` needs `[CharZero k]`); a computation lemma for `Y0LevelPoints` on the exact-order cover; the lift of a cover point to `W(k)` (the cover is finite étale over `ShortBase R`, `universalExactOrder_finite_etale`; Hensel for smooth morphisms, EGA IV 18.5.17, UNVERIFIED); item 3 over an algebraic closure of `Frac W(k)`; reduction of the Vélu quotient and of separable seams (Silverman VII.3.1, UNVERIFIED). |
| Uniqueness in char. ℓ (downstream of point_W, not of item 4) | Two separable isogenies out of `E` with kernel `C_Q` differ by an isomorphism of their targets, over `k` algebraically closed of characteristic ℓ. | Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., 2009, III.4.11–4.12 (UNVERIFIED). Missing from the tree. Needed by the consumer of item 4, since the X.W side supplies its own Q-isogeny and the witness of item 4 is not named. |
| `point_W` | `point (X.W q x) = point x ≫ special.map Wint`. | Needs item 4 and `point` (hCM lane). Not stated as supplied. |

## What `Relations` needs (no Hecke item in this run)

`Relations ap` (`RC/PMWire/Operators.lean:143–145`) has two parts: `hecke`, a `HeckePacket q x` for every good `q ∤ N ell` and supersingular `x`, and `eigen`, a `HeckeIdentity`. A `HeckePacket` (`Operators.lean:122`) consists of the following.
- `B`, a smooth `Over (Spec R)`, with `source : B ⟶ G.M` and `q+1` maps `target j : B ⟶ G.M`. This is an integral good Hecke correspondence on the pinned model. Owner: a model lane; this run builds no correspondence object.
- `lift : residueSource ⟶ special B` with `source_eq` and `target_eq` through `G.point`. Owner: the same-place lane (hCM), since both go through `point`.
- `neighbour` and `divisor_eq : X.T q x = Σ neighbour`. Owner: the coarse-fibre (adelic/hCM) side.

`eigen` is the generic-fibre identity `∏_j (target j ≫ πInt) = (source ≫ πInt)^{a_q}` on the generic fibre. Owner: the generic Hecke comparison (generic4 item 4, open) plus the intertwining of `T_q` with `[a_q]` on the elliptic quotient.

## Tiers for `point_W`

| Tier | Statement | Status |
| --- | --- | --- |
| Done | Integral `W` on the pinned model, extending `rationalW`; unique; involution; complex points read as matrix translates | this run |
| Next | Item 3 (char. 0) above: choice-free over seams, for every representative and every seam | open; continued in rc-model-generic6 |
| Then | Item 4 (char. ℓ) above: existential over separable seams | open; continued in rc-model-generic6 |
| Downstream | `point_W` itself, against the hCM lane's `point` and the coarse fibre's `X.W` | open |

## Known issues

- Inherited: the Milne locators at tex 1784–1788 do not state the normalized-newform and Hecke claims.
- Inherited: Jetchev–Kane (arXiv v1; journal version unread), cited at tex 8468–8474, refers the class correspondence to Ribet 1990 Prop. 3.3. It does not print the Hecke, Atkin–Lehner or Frobenius compatibilities. Ribet's Prop. 3.3 and Rem. 3.5 are reported with proofs deferred (Milne 1979, Carayol 1986, Vignéras), so they are never sources; Ribet 1990 Prop. 3.6 is the citable converse. The level-N correspondence is being built in the hCM lane from Voight's maximal-level statements. All UNVERIFIED.
- Katz–Mazur 1985 §2.4 (cited in the generic4 tiers) could not be checked and is marked UNVERIFIED there. For GoodRow.extension the citation is no longer needed (`extendsAtkin_Wint`). The special-fibre action that point_W needs (item 4) is still open.
- Technical: the synthesized `CommRing` instance on `Pinned.Y0LevelAlgebra` takes a path that does not unify cheaply with `Subalgebra.toSemiring`; the result is `whnf` timeouts at 10⁶ heartbeats. `Extension.lean` declares `levelCommRing := Subalgebra.toCommRing _` as a local instance of priority 2000. Downstream files that mix `levelToRat`/`atkinLevel` with `Pinned.Y0Level` should do the same.
- Route deviation (allowed by the brief): item 2(a) uses the function-field route. This means integral closure over `ℚ[j]` of the actual pullback, plus the generic-point comparison. It does not use the closed-point/Jacobson route. It ties (a) to (c), as the brief noted.

## Manuscript check

| TeX lines | Verdict | Step |
| --- | --- | --- |
| 8366–8368 | OK | The stage place excludes two, all bad primes, the support of `D_w h_*` and any other finite set. In Lean, stage primes are odd, prime to `Δ(E_ℓ) = 2⁸3²ℓ⁶` (so `≥ 5`), and avoid the Setup's set `B`. `htame` follows once `B ⊇` primes of `N φ(N)`. |
| 8476–8478 | supporting | "The modular curve has good reduction": the smooth pinned model is from the levels lane; this run uses it as the source of `Wint`. |
| 8478–8479 | unverified | "The good Hecke correspondences also extend": not touched (`Relations`, see above). |
| 8487–8489 | gap filled (implicit step) | `W_{p^e}`: the tex uses the integral operator here without stating it. The Atkin–Lehner involution `W_{q^{v_q N}}` extends to the pinned smooth model, uniquely, as an involution (`extendsAtkin_Wint`, `eq_Wint_of_extendsAtkin`, `Wint_comp_self`); **ON THE SPOT (c)**: integral closure plus reduced special fibre. It acts on complex points as the matrix translate. The eigenvalue identity and the moduli form on points (item 3) are not touched. |
| 9101–9113 | reduced to the listed inputs | (O.7) is derived in Lean from the listed inputs (oddStagedOfSamePlace); this run supplies GoodRow.extension and the stage-prime hypotheses. |
| ON THE SPOT (conductor; no tex locator) | OK | The level `N` of `E_ℓ` is at least 2 (`two_le_level`, from `hN`). |
| 1784–1788 | unverified | Inherited citation scope. |
