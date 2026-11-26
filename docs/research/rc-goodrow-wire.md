# The assembled GoodRow at every stage prime

**Retired frozen field:** none yet. This run retires no field of `frozenTarget` and changes no GLUE
count. The frozen row is the `hRC` GLUE row (`docs/one-proof/OPEN.md`, section `hRC`); its odd-side
input is `PreLeaves.odd_staged` (`ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean:305`). No frozen field
is retired until the same-place data `sp` (and the other remaining hypotheses below) are also supplied.

**Error verdicts:** none.

**Main result.** `GoodRowWire.oddStagedOfSamePlace` (`RC/GoodRowWire/Assembly.lean`) is
`PMWire.oddStagedOfGoodRows` (`RC/PMWire/Assembly.lean:220`) with its hypotheses `G` and `hcop`
replaced. Every `GoodRow` field other than the four same-place fields is now the actual object of its
lane. `stageRow` (`RC/GoodRowWire/Row.lean`) assembles the row at every stage prime, and the same-place
fields form one explicit input, `SamePlaceData` (`RC/GoodRowWire/SamePlace.lean`). All three modules
build with `lake build`. They contain no `sorry` and no axiom declaration, and `#print axioms` of every
new declaration gives only `propext`, `Classical.choice` and `Quot.sound`.

**Accounting.** G and hcop are replaced by hB and sp; hcop and htame are derived from hB
(`GoodRowWire.stage_coprime`, `ModelGeneric5.stagePrime_not_dvd_tame`); h2 comes from
`two_le_level hN`. h5 comes from `ModelGeneric5.stagePrime_five_le s i`, and hΔ from
`StageKummer.goodAt s i`. In the restated theorem no free `G`, `hcop` or `R` is left. The substitution is
`R i := LocalIntegers (s.q.stage i).p`, `G := stageRows a s π hQ hN hB sp`
(`= fun i => stageRow s hN hB π hQ i (sp i)`) and `hcop := stage_coprime s hN hB`. It is applied in
`J`, `relations`, `cusps`, `refs` and `ha`, whose content is otherwise unchanged.

## Per-field GoodRow table (`stageRow s hN hB π hQ i S`)

Here `p := (s.q.stage i).p`, `N := StageKummer.level ℓ`, `h₅ := stagePrime_five_le s i`,
`htame := stagePrime_not_dvd_tame s hN hB i` and `h₂ := two_le_level hN`.

| Field | Supplied by (lane, theorem) |
| --- | --- |
| `closed` | neron lane: `ModelNeron.closed p` (hardwired by `GoodTarget.toGoodRow`; `stageRow_closed`) |
| `M` | levels lane: `Pinned.Y0Level h₅ htame h₂` (`stageRow_M`) |
| `smoothM` | levels lane: `Pinned.Y0Level_smooth` |
| `reducedM` | neron lane: `ModelNeron.reducedM` |
| `separatedM` | neron lane: `ModelNeron.separatedM` |
| `denseGeneric` | neron lane: `ModelNeron.denseGeneric` |
| `source` | neron lane: `ModelNeron.source h₅ htame h₂` (`stageRow_source`) |
| `E`, `groupE`, `neron`, `jE`, `properGenericE`, `geomIntGenericE` | target lane: `ModelTarget.goodTarget p (EcurveZ ℓ) _ h₅ (StageKummer.goodAt s i)`. `E = detE p (EcurveZ ℓ)` (`stageRow_E`), `weierstrassModelGrp`, `weierstrassModel_isNeron`, `cubicJE`, `detProperGeneric`, `detGeomIntGeneric` |
| `readComplex`, `readComplex_eq` | target lane: `readComplexCubic`, `readComplexCubic_eq` |
| `read`, `read_frob` | target lane: `ModelTarget.read`, `ModelTarget.read_frob` |
| `extension` | generic5 lane: `ModelGeneric5.goodRow_extension h₅ htame h₂` (witness `Wint`). `stageRow_W`: the row's `W q hq he` is `Wint` (`eq_Wint_of_extendsAtkin`) |
| `point` | same-place lane: `S.point` (`stageRow_point`) |
| `point_W` | same-place lane (the hCM lane): `S.point_W`, converted to the `GoodRow` form by `SamePlaceData.point_W_choose`; also needs the special-fibre action of `Wint` (generic5 item 4, not started) |
| `point_frob` | same-place lane: `S.point_frob` |
| `frobenius_sq` | same-place lane: `S.frobenius_sq` |

Every type equality in the assembly holds by definitional unfolding, so no bridge or cast was needed:

* `K = ResidueAt (StageKummer.place s i)`;
* `Ebar = ReducedEquation (EcurveZ ℓ) p`: goodTarget's `ReducedEquation W₀ ell` at `W₀ := EcurveZ ℓ`;
* `E₀ = (EcurveZ ℓ)⁄ℚ`: `IsElliptic` is a Prop class, so goodTarget's `detRational_isElliptic hΔ` and the
  consumer's instance agree;
* `fixedMap π hQ`, whose source is `Over.mk (X0Model3.model N).overQ`, against `rationalSource N`
  (`= Over.mk (X0Branch.model N).overQ`), the compact source of `ModelNeron.source`; this is the same
  type at which `oddStagedOfGoodRows` already takes `G`;
* `PMWire.genericProjection` against `ModelNeron.denseGeneric`, as already used in
  `eq_Wint_of_extendsAtkin`.

The file uses `open scoped Classical`, as `Assembly.lean:11` does, so the `DecidableEq` instance on
`ResidueAt` is the one in `G`'s type. The stage-prime `Fact` instance is the global
`O7Assemble.stagePrime` (`RC/O7Assemble/ActualFamily.lean:19`), the same one that
`PMWire.Assembly` uses.

## New declarations

`RC/GoodRowWire/SamePlace.lean`

* `structure SamePlaceData (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N) (K) (X)` has
  exactly the fields `point`, `point_W`, `point_frob` and `frobenius_sq` of `GoodRow`, on
  `Pinned.Y0Level h₅ htame h₂` with `closed := ModelNeron.closed ell`. They have the `GoodRow` types,
  except that `point_W` uses `ModelGeneric5.Wint h₅ htame h₂ (isExactDivisor_primePow (N := N) (p := q))`
  in place of `(extension q hq he).choose`. Owner: the same-place lane in the hCM lane (tex 8479–8492).
  It is an input, never a leaf.
* `SamePlaceData.point_W_choose` turns `point_W` into the exact `GoodRow.point_W` form for any family
  `ext` of extensions. The proof rewrites by `eq_Wint_of_extendsAtkin` (`PMWire.extendsAtkin_unique`).
  `eq_Wint_of_extendsAtkin` needs neither `q.Prime` nor `q ∣ N`, so no conversion from
  `0 < N.factorization q` is needed.

`RC/GoodRowWire/Row.lean`

* `stage_coprime s hN hB : ∀ i, (StageKummer.level ℓ).Coprime (s.q.stage i).p` is the `hcop` of
  `oddStagedOfGoodRows`, derived from `hB` through `stagePrime_not_dvd_tame`.
* `abbrev StageSamePlace s hN hB X i := SamePlaceData h₅ htame h₂ (ResidueAt (StageKummer.place s i)) X`
  is the same-place input at stage `i`.
* `def stageRow s hN hB π hQ i (S : StageSamePlace s hN hB X i) : GoodRow (LocalIntegers p) p N
  (ResidueAt (StageKummer.place s i)) (ReducedEquation (EcurveZ ℓ) p) X (fixedMap (C := EcurveZ ℓ) π hQ)`.
  It is `(goodTarget …).toGoodRow` applied to the pinned model, its source, `S.point`,
  `goodRow_extension`, `S.point_W_choose _`, `S.point_frob` and `S.frobenius_sq`.
* `stageRow_closed`, `stageRow_M`, `stageRow_source`, `stageRow_E`, `stageRow_point` (all `rfl`) and
  `stageRow_W` (the row's integral Atkin–Lehner operator is `Wint`) record that each field is the lane's
  actual object.

`RC/GoodRowWire/Assembly.lean`

* `abbrev stageRows a s π hQ hN hB sp i := stageRow s hN hB π hQ i (sp i)`.
* `theorem oddStagedOfSamePlace` takes the hypotheses of `oddStagedOfGoodRows` except `G` and `hcop`,
  in the binder order `hB, sp, J, relations, cusps, H, hm, refs, ha, hL, hsign`. Its conclusion is
  `Nonempty (OddStagedInstance (withParamIndices a))`. The proof is `oddStagedOfGoodRows` at
  `hcop := stage_coprime s hN hB` and `G := stageRows a s π hQ hN hB sp`.

## What remains

| Hypothesis of `oddStagedOfSamePlace` | Owner lane |
| --- | --- |
| `sp` (`point`, `point_W`, `point_frob`, `frobenius_sq` at each stage) | same-place lane (hCM lane) |
| `hB : (N φ(N)).primeFactors ⊆ s.B` | stage lane (choice of exclusion set; satisfiable, see below) |
| `J` (`PMAdelic.JetchevKane`) | hCM lane (class correspondence GLUE, three compatibilities ELLIOT) |
| `relations` (`Relations`: `hecke`, `eigen`) | detector-specialization lane |
| `cusps` (Manin–Drinfeld torsion, `KillsTranslation`) | J0Cusps lane |
| `H`, `hm` | stage lane (discriminant data) |
| `refs` (`Reference`: embedding, orientation, CM reductions, `hCM`, `diagram`) | hCM lane (CM points) |
| `ha` (aθ definition pin, tex 2081–2082) | O.7 lane |
| `hL`, `hsign` | theta side / sign lane |
| `π`, `hQ` (the fixed parametrization `X0Model3.model N ⟶ Proj` of `(EcurveZ ℓ)⁄ℚ` over `ℚ`) and `han` (its complex points are `phiAn` of the newform; a substantive input) | the fixed parametrization, unchanged from `oddStagedOfGoodRows` |
| `F` (`ConsumerNewform`), `hN : 0 < N` | newform data, as in `oddStagedOfGoodRows` |
| instance arguments `[NeZero (CST.newformLevel (Ecurve ℓ))]`, `[NeZero (StageKummer.level ℓ)]`, `[((EcurveZ ℓ)⁄ℚ).IsElliptic]` | as in `oddStagedOfGoodRows` |
| `X : ℕ → PMAdelic.CoarseFibre` | fixed by `J`'s owner (hCM lane); `sp` must be supplied for the same `X` |

`hB` is satisfiable. When the setup comes from `Stages.exists_detector_stages`, `s.B` is
`stageExclusions ℓ Dw hstar B'` (`RC/Stages/DetectorStages.lean:48–49`, `RC/Stages/Actual.lean:99`).
`ModelGeneric5.subset_stageExclusions` gives `B' ⊆ s.B`, so any `B' ⊇ (N φ(N)).primeFactors` satisfies
`hB`. Manuscript: tex 8366–8368, where the place for `l₀` is chosen to "exclude two, all bad primes, the
support of D_w h_* and any other finite set". No `Setup` is built here.

## What the same-place lane must supply (per stage `i`, `p := (s.q.stage i).p`)

| Field | Type (on `M := Pinned.Y0Level h₅ htame h₂`, `K := ResidueAt (StageKummer.place s i)`) | Manuscript |
| --- | --- | --- |
| `point` | `(X i).Point → (residueSource p K ⟶ (Over.pullback (Spec.map (ofHom (ModelNeron.closed p)))).obj M)` | tex 8479–8492 (supersingular points as special-fibre points) |
| `point_W` | `∀ q hq he x, point (W q x) = point x ≫ (pullback).map (Wint h₅ htame h₂ (q ^ v_q(N) ∥ N))` | tex 8486–8488 (Atkin–Lehner `W_{p^e}`); needs the special-fibre action of `Wint` (generic5 item 4, not started) |
| `point_frob` | `∀ x, point (frobenius x) = residueFrob p K ≫ point x` | tex 8489–8490 ("Frobenius acts on the supersingular set as the right division-uniformizer operation") |
| `frobenius_sq` | `Function.Involutive (X i).frobenius` | tex 8489–8492 (uniformizer eigenvalue `+1`) |

## Known issues

* Inherited: the Milne locators at tex 1784–1788 do not state the normalized-newform and Hecke claims.
* Inherited: Jetchev–Kane (arXiv v1; journal version unread), cited at tex 8468–8474, attributes the class
  correspondence to Ribet 1990 Prop. 3.3. It does not print the Hecke, Atkin–Lehner or Frobenius
  compatibilities. The lead's ruling splits the `JetchevKane` structure: the class correspondence is
  GLUE, and the three compatibilities are ELLIOT, to be proved in Lean. The hCM lane builds the
  correspondence in Lean from Voight's maximal-level Deuring statements. Ribet 1990 Prop. 3.6 (Invent.
  Math. 100 (1990); UNVERIFIED), which is proved there, is the citable converse. Ribet's Prop. 3.3 and
  Rem. 3.5 defer their proofs to Milne 1979, Carayol 1986 and Vignéras, so they are never cited as sources.
* `relations`, `cusps` and `refs` are stated over `stageRows`, so their owners must supply them on the
  pinned model `Pinned.Y0Level` and the good cubic `detE`. In particular, `HeckePacket.source_eq` and
  `target_eq` refer to `S.point`.
* Degenerate witnesses. `SamePlaceData` fixes `point` only up to an equivariant choice on each orbit:
  post-composing `point` with the special-fibre map of `Wint_q0` preserves the four fields, as it already
  does in `PMWire.GoodRow`. A constant `point` is ruled out: `point_frob` forces it to be `F_ell`-rational,
  and `point_W` would need a common fixed point of every `Wint_q`; `X.frobenius` is pinned by
  `J.frobenius` on `X.ss` (`RC/PMAdelic/Comparison.lean:89–90`). Faithfulness is carried by `refs`
  (`CMDiagram.sourceResidue`, `RC/PMWire/CM.lean:163`; `Reference.hCM`, `RC/PMWire/Assembly.lean:168–174`)
  and `relations` (`HeckePacket.source_eq` and `target_eq`), which are typed over the same
  `stageRows … sp`. So `sp`, `refs` and `relations` must come from one construction of `point`.

## Manuscript check

| TeX lines | Verdict | Step |
| --- | --- | --- |
| 1784–1788 | unverified | Inherited literature scope for the newform and Hecke claims. |
| 2081–2082 | OK | `ha`, the aθ integer representative pin, is carried unchanged. |
| 8366–8368 | OK | The place for `l₀` excludes any finite set; `hB` asks that `s.B` contain the primes of `N φ(N)` (gives `hcop`, `htame`). |
| 8476–8477 | OK | "`ℓ₀ ∤ N`": `stage_coprime` from `hB`. |
| 8477–8478 | gap filled | Good reduction of the modular curve: pinned model of the levels lane at `h₅`, `htame`, `h₂`. |
| 8478–8479 | gap filled | The good-reduction elliptic curve and the extension of the map: `goodTarget` with `hΔ := goodAt s i`; `πInt` through `weierstrassModel_isNeron`. |
| 8486–8488 | gap filled (extension); open (`point_W`) | Atkin–Lehner over the local base: `Wint` (generic5); its action on the special-fibre points is in `sp`. |
| 8489–8492 | open (input) | Frobenius on the supersingular set: `point_frob` and `frobenius_sq` in `sp`. |
| 9101–9113 | reduced to the listed inputs | (O.7) is derived in Lean from the listed inputs (`O7Actual`'s `DatumAt.representative`, `RC/O7Actual/Family.lean:111`, converts `DatumAt.reduce` into the (O.7) shape, but the actual `DatumAt` is built from `J`, `G` (now `stageRows … sp`), `relations`, `cusps` and `refs`); the wiring feeds `oddStagedOfGoodRows`. |

Provenance: everything in this run is wiring, on the spot (c). No new leaf and no print.
