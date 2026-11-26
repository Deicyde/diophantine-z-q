# The integral elliptic model at the detector

## Error verdicts

None.

## Retired frozen fields and GLUE rows

None yet. This lane retires no field of `frozenTarget` and changes no GLUE count. The `hRC` GLUE row
(`docs/one-proof/OPEN.md`, section hRC: `docs/one-proof/OPEN.md#hrc`) and its odd-side input `PreLeaves.odd_staged`
(`ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean:305`) still need the `PMWire.GoodRow` fields owned by
other lanes:

* `point`, `point_frob` and `frobenius_sq` (same-place comparison);
* `point_W`: an input of `SamePlaceData`, owned by the same-place lane (the hCM lane); it also needs
  the special-fibre action of `Wint` (generic5 item 4, not started). (`extension` is supplied by
  `ModelGeneric5.goodRow_extension`, witness `Wint`.)
* `ha`, the aθ definition pin (tex 2081–2082; `RC/PMWire/Assembly.lean:221–233`, consumed at
  `RC/O7Actual/Family.lean:121`) that `PMWire.oddStagedOfGoodRows`
  (`ZInQKernel/Contrib/OneProof/RC/PMWire/Assembly.lean:220`) takes. (O.7)
  is derived in Lean from the listed inputs (`O7Actual`'s `DatumAt.representative`, `RC/O7Actual/Family.lean:111`, converts `DatumAt.reduce` into the (O.7) shape, but the actual `DatumAt` is built from `J`, `G` (now `stageRows … sp`), `relations`, `cusps` and `refs`);
* the other inputs of `oddStagedOfGoodRows`: `refs`, `J`, `relations`, `cusps`, `hL` and `hsign`.

## Main result

Every target-side field of `PMWire.GoodRow` (`ZInQKernel/Contrib/OneProof/RC/PMWire/Model.lean:35` on
main) is now supplied by the good integral Weierstrass cubic itself. Items 1–5 of the brief are complete,
with no leaf and no hypothesis beyond the detector data.

Fix a prime `ℓ` with `5 ≤ ℓ`, the detector ring `R = ModelTorsion.LocalIntegers ℓ`, and an integral
Weierstrass equation `W₀ : WeierstrassCurve ℤ` with `¬ ℓ ∣ Δ(W₀)`. Put `W = detW ℓ W₀ = W₀.map (ℤ → R)`.
The good cubic is `E = detE ℓ W₀ = ModelNeron.weierstrassModel ℓ W`, the `Proj` of the graded
Weierstrass coordinate ring over `R`. The fixed rational and reduced equations are `E₀ = W₀⁄ℚ` and
`Ebar = ReducedEquation W₀ ℓ`.

The good equation is carried as detector data, as the brief asks. Prime naming at the consumer: the
lane prime `ℓ` of this report is the stage prime `(s.q.stage i).p` of `PMWire.oddStagedOfGoodRows`
(not the curve index `ℓ` of `EcurveZ ℓ`); `W₀ := EcurveZ ℓ`, so `E₀ = (EcurveZ ℓ)⁄ℚ` and
`Ebar = ReducedEquation (EcurveZ ℓ) (s.q.stage i).p` as in `RC/PMWire/Assembly.lean:120–122`; and `hΔ`
is `StageKummer.stageGood` (`RC/StageKummer/Actual.lean:262`), in the form `StageKummer.goodAt s i`
(`RC/StageKummer/Reference.lean:67–70`). Good reduction is never derived from `π`, `J₀(N)` or the
conductor.

Every declaration below builds with `lake build` and has no `sorry` or `axiom` declaration. Its
`#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`.

| Field of `GoodRow` | Supply |
| --- | --- |
| `closed` | supplied: `ModelNeron.closed` (neron lane) |
| `M`, `smoothM`, `reducedM`, `separatedM`, `denseGeneric`, `source` | supplied: `Pinned.Y0Level`, `ModelNeron.*` (levels and neron lanes) |
| `E` | supplied: `detE ℓ W₀`, the cubic |
| `groupE` | supplied: `weierstrassModelGrp` (`RC/ModelTarget/GroupObj.lean:92`) |
| `neron` | supplied: `weierstrassModel_isNeron` (`GroupObj.lean:99`) |
| `jE` | supplied: `cubicJE` (`CubicComplex.lean:106`; the same composite as `detGenericIso`, `DetectorModel.lean:83`) |
| `properGenericE` | supplied: `detProperGeneric` (`DetectorModel.lean:89`) |
| `geomIntGenericE` | supplied: `detGeomIntGeneric` (`DetectorModel.lean:95`) |
| `readComplex` | supplied: `readComplexCubic` (`CubicComplex.lean:147`) |
| `readComplex_eq` | supplied: `readComplexCubic_eq` (`CubicComplex.lean:170`) |
| `read` | supplied: `read` (`ReadEquiv.lean:84`) |
| `read_frob` | supplied: `read_frob` (`ReadEquiv.lean:108`) |
| `point`, `point_frob`, `frobenius_sq` | open: same-place comparison lane (hCM's v21g builds the supersingular pair classes first) |
| `extension` | supplied: `ModelGeneric5.goodRow_extension` (witness `Wint`) |
| `point_W` | open: input of `SamePlaceData`, owned by the same-place lane (the hCM lane); also needs the special-fibre action of `Wint` (generic5 item 4, not started) |

`goodTarget ℓ W₀ K h₅ hΔ : GoodTarget ℓ K (ReducedEquation W₀ ℓ) (W₀⁄ℚ)` (`Supply.lean:52`) packages the
ten supplied fields. `GoodTarget` (`Supply.lean:28`) lists exactly the corresponding fields of `GoodRow`,
with `closed := ModelNeron.closed ℓ`. `GoodTarget.toGoodRow` (`Supply.lean:71`) builds a
`PMWire.GoodRow` from a `GoodTarget` and the remaining fields, so the supplied fields have exactly the
consumer's types.

The second supply for `E`, `neron`, `jE`, `properGenericE` and `geomIntGenericE` is also complete. This is
the local Néron target `ModelNeron.localTarget`, with existence PROVED as `dvrLocal_of_extension ∘
neronSchemeExtensionExists_of_dedekind ∘ neronSchemeExtensionDedekind_proof`. Here that existence enters
only as the closed term `ModelTarget.neronDVRLocal` (`LocalReading.lean:30`). Its group law `neronLaw` is
transported from the rational law through the Néron property, and `localReadComplex` reads its complex
points. The cubic remains the preferred `E`, because `read` and `read_frob` are the actual reduction of
the points of `W`. An isomorphism `LocalTarget.E ≅ E` (uniqueness of Néron models) is optional and was not
built.

## What was built

### Item 1: smoothness and base change (on the spot, c)

* `ChartRing.lean`. `Chart W i` is the chart `D₊(Xᵢ)`. The file defines `chartConst`, `ratio`,
  `dehomogenize`, `chart_equation`, `chart_ringHom_ext`, `chartLift` and `chartEquiv`. A dehomogenization
  together with a map back identifies a chart with any presentation of the affine piece.
* `ChartPresentation.lean`. `zyEquiv : W.toAffine.CoordinateRing ≃+* Chart W 2` presents the `Z`-chart.
  `zxEquiv` presents the `Z`-chart as monic in `x`. `yEquiv hw` presents the `Y`-chart after the shear
  `x = x' + cz`, where `w (c³ + a₂c² + a₄c + a₆) = -1`.
* `ChartSmooth.lean`. `smooth_away_derivative`: a monic polynomial over `R[X]`, localized at its
  derivative, is smooth over `R` (Mathlib's `StandardEtalePair`). `span_partials_zChart`: the two partials
  generate the unit ideal, because a common zero with values in a field would be singular.
  `smooth_chartZ : RingHom.Smooth (chartConst W 2)`.
* `ChartSmoothY.lean`. `smooth_chartY : RingHom.Smooth (chartConst W 1)`. It is proved from the sheared
  derivative and `z`, and from the overlap `D₊(YZ)`, which is a localization of the smooth `Z`-chart.
* `WeierstrassSmooth.lean`. `iSup_basicOpen_YZ`: the charts `D₊(Y)` and `D₊(Z)` cover. Then
  `smooth_projStructure`. `exists_shear` finds a shear among `0,1,2,3` because the third finite
  difference of a monic cubic is `6`. **`weierstrassModel_smooth h₅ W₀ hΔ : Smooth E.hom`** is one of the
  two named instances.
* `BaseChange.lean`, `BaseChangeInv.lean`, `BaseChangeIso.lean`. **`bcIso W ψ : (Over.pullback (Spec.map
  ψ)).obj (cubic W) ≅ cubic (W.map ψ)`** holds for any ring map `ψ`. It is the identity in homogeneous
  coordinates (`bcVec`, `invVec`). The two maps are built by `morphism_of_rule` and are mutually inverse at
  field points.
* `DetectorModel.lean`. It proves `smooth_mapped`, `reduced_mapped` and `reduced_baseChange`, and builds
  `detFibreIso ψ` for any field. With that it builds **`detGenericIso : (generic R ℚ).obj E ≅
  PMWire.ellipticTarget (W₀⁄ℚ)`**, the generic pullback, and proves `detProperGeneric` and
  `detGeomIntGeneric`. The residue pullback is `detFibreIso (ModelNeron.closed ℓ)`. Since
  `(detW ℓ W₀).map closed = ReducedEquation W₀ ℓ` (`detW_map_eq`), it identifies the special fibre with
  the projective cubic of `Ebar`.

### Item 2: the group object over `R` (on the spot, c; the manuscript constructs nothing here)

The rational law of `J0Cusps.projectiveGroup_exists` uses a short-form change of variables and is
specialized to `ℚ`. This lane instead glues two complete addition laws defined over any ring. One is
Mathlib's `addXYZ`, attached to the line `Z = 0`. The other is Tau Ceti's `dblAddXYZ`, attached to
`Y = 0`. These are the laws of W. Bosma and H. W. Lenstra Jr., *Complete systems of two addition laws for
elliptic curves*, J. Number Theory 53 (1995), Theorem 2 (UNVERIFIED). Their field-level facts are proved in
the vendored Tau Ceti port: `addXYZ_ne_zero_or_dblAddXYZ_ne_zero`, `dblAddXYZ_equiv_add`,
`Equation.addXYZ` and `Equation.dblAddXYZ`.

* `ChartMorphism.lean`. `chartMorphism` is a morphism `Spec A ⟶ Proj W` given by a solution vector with a
  unit coordinate. `chartMorphism_independent` and `chartMorphism_smul` show it depends only on the point.
  `chartMorphism_map` gives naturality. `eq_chartMorphism`: every map of base schemes into a chart is a
  chart morphism.
* `FieldValue.lean`. `fieldValue` reads a field point as an affine point of `W.map g`.
  `equiv_of_chartMorphism_eq` shows the vector is unique up to a unit, and `fieldValue_injective` holds.
* `FormulaGluing.lean`, `FormulaMorphism.lean`, `RuleGluing.lean`. `morphism_of_formulas` and
  `morphism_of_rule` are the relative form of `J0Cusps.projectiveMorphism_of_formulas`. Agreement on
  overlaps is checked at field points, using a reduced source and a separated cubic.
* `GroupLaw.lean`. `cubicOne` is `(0 : 1 : 0)`. `cubicInv` is `(X : -Y - a₁X - a₃Z : Z)`. `cubicMul` is
  glued from the two laws. `val_one`, `val_inv` and `val_mul` say these compute Mathlib's group law at
  every field point.
* `GroupObj.lean`. `cubicGrp` proves the group axioms at field points. The products of the smooth cubic are
  reduced by `isReduced_of_smooth_hom`. **`weierstrassModelGrp h₅ W₀ hΔ : GrpObj E`** is the second named
  instance. **`weierstrassModel_isNeron`** gives `CToPrinted.IsNeronModelOver R ℚ E` (item 3).

### Items 4 and 5: the readings (on the spot, c)

* `ComplexReading.lean` is item 4 in generic form. `readComplex E jE g hg hj` works for any integral group
  model whose generic identification is a homomorphism to a law with chord-and-tangent complex points
  (`IsComplexLaw`). `readComplex_eq` is `rfl`.
* `LocalReading.lean` instantiates item 4 at `LocalTarget.E`, through `neronLaw` and
  `NeronC.isMonHom_of_neron`.
* `PullbackMul.lean`. `mul_left_fst`: points of a base-changed group object multiply as their images.
* `CubicComplex.lean` is item 4 at the cubic. `projectiveValue_eq_fieldValue` identifies `J0Cusps`'s
  value with `fieldValue`. `projectiveValue_cubicJE` and `readComplexCubic` follow, and
  `readComplexCubic_eq` is `rfl`.
* `Read.lean` and `ReadEquiv.lean` are item 5. A residue point `y` of the special fibre is the point
  `y ≫ fst` of `Proj W` over `R → 𝔽_ℓ → K`. `read y` is its value on `Ebar⁄K`, so the reading is the
  actual reduction of the points of `W`. It is multiplicative (`readFun_mul`) and bijective
  (`readFun_injective`, `readFun_surjective`). `read_frob` holds because `map_toAffine` moves Frobenius
  through `toAffine`.
* `Supply.lean` contains `GoodTarget`, `goodTarget` and `GoodTarget.toGoodRow`.

## Leaves used

None. The lane adds no printed-form statement. Nothing here is a leaf:

* `NeronDVRLocal` enters only as the closed term `neronDVRLocal`, in the optional `LocalTarget` route.
* The Bosma–Lenstra laws come from the vendored Tau Ceti port, with proofs.
* `isReduced_of_smooth_hom` calls a vendored proved theorem; see Known issues.

## Remaining

| Item | Status and reduction |
| --- | --- |
| `point`, `point_frob`, `frobenius_sq` | Other lane (same-place comparison). Ribet, *On modular representations of Gal(Q-bar/Q) arising from modular forms*, 1990, Prop. 3.6 (proved there) UNVERIFIED. The level-N correspondence is being built in the hCM lane from Voight, *Quaternion Algebras*, GTM 288, 2021, Thm. 42.1.9 and 42.3.2 (two-lens pass pending). |
| `extension` | Supplied by `ModelGeneric5.goodRow_extension` (witness `Wint`). |
| `point_W` | Other lane: an input of `SamePlaceData`, owned by the same-place lane (the hCM lane); it also needs the special-fibre action of `Wint` (generic5 item 4, not started). |
| `ha`, the aθ definition pin, and the other inputs `refs`, `J`, `relations`, `cusps`, `hL`, `hsign` of `oddStagedOfGoodRows` | Other lanes. `ha` (tex 2081–2082; `RC/PMWire/Assembly.lean:221–233`, consumed at `RC/O7Actual/Family.lean:121`) pins the integer representative aθ; (O.7) is derived in Lean from the listed inputs (`O7Actual`'s `DatumAt.representative`, `RC/O7Actual/Family.lean:111`, converts `DatumAt.reduce` into the (O.7) shape, but the actual `DatumAt` is built from `J`, `G` (now `stageRows … sp`), `relations`, `cusps` and `refs`). |
| `LocalTarget.E ≅ E` (optional) | Not built. It follows from the Néron mapping property both ways: both are Néron models of `W₀⁄ℚ`, now proved, together with `cubicJE` and `LocalTarget.jE`. BLR, *Néron Models*, 1990, §1.2 Def. 1 UNVERIFIED. Lean work only, with no new input. |
| Compatibility of `cubicJE` with the `J0Cusps` scheme law | Not needed by `GoodRow`, which asks only for the complex reading. It would follow from `val_mul` and `projectiveValue_eq_fieldValue` at all field points. |

## Known issues

* Inherited: the Milne locators at tex 1784–1788 do not state the normalized-newform and Hecke claims.
* Inherited: Jetchev–Kane (tex 8468–8474; arXiv v1, journal version unread) attributes the class
  correspondence to Ribet 1990 Prop. 3.3. It does not print the Hecke, Atkin–Lehner or Frobenius
  compatibilities. Ribet's Prop. 3.3 and Rem. 3.5 defer their proofs to Milne 1979, Carayol 1986 and
  Vignéras, so they are never cited. Ribet 1990 Prop. 3.6 (Invent. Math. 100 (1990); UNVERIFIED), which is
  proved there, is the citable converse.
  The lead's ruling splits the `JetchevKane` structure: the class correspondence is GLUE, and the three
  compatibilities are ELLIOT, to be proved in Lean.
* `isReduced_of_smooth_hom` (`GroupObj.lean:21`) calls the vendored theorem
  `ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian.solution`
  (`ZInQKernel/Contrib/CloudR2NOS/Source/P2M/Sol/`). It is fully proved, with standard axioms. Its file
  header calls it a "probe staging copy" of the FLT port, held outside H5. Smooth
  maps are geometrically reduced by `isReduced_of_smooth_of_field`, then Mathlib's
  `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian` applies. The reviewer may prefer to
  rebind it.
* `cubicJE` is the composite `bcIso ≪≫ eqToIso (W₀.map (ℤ→R) .map (R→ℚ) = W₀⁄ℚ)`. It is `detGenericIso`
  unfolded through `detFibreIso`, but `detGenericIso` is not syntactically `cubicJE`. A `rfl` proof of
  their equality timed out during unification, so `GoodTarget.jE` uses `cubicJE`.
* The tree has no Mathlib-style lemma identifying `Proj` of a base-changed graded ring with a pullback.
  `bcIso` is specific to the Weierstrass cubic.

## Manuscript check

| TeX lines | Verdict | Step |
| --- | --- | --- |
| 1784–1788 | unverified | Inherited literature scope for the newform and Hecke claims. |
| 8364–8368 | OK | The detector avoids the bad primes. The good equation's discriminant is prime to `ℓ` (`hΔ`); the frozen route gets this from `stage_facts`. |
| 8476–8478 | gap filled | "The modular curve has good reduction" is the source side, from the levels lane. |
| 8477–8479 | gap filled | "The good-reduction elliptic curve": its projective cubic over `ℤ_(ℓ)` is smooth (`weierstrassModel_smooth`), a group scheme (`weierstrassModelGrp`) and a Néron model (`weierstrassModel_isNeron`). Its generic fibre is the fixed rational cubic (`detGenericIso`) and its special fibre is the reduced cubic (`detFibreIso`, `detW_map_eq`). |
| 8478–8479 | gap filled | "The map extends over the local base": with `E` the cubic, `GoodRow.πInt` is the Néron extension through `weierstrassModel_isNeron`. |
| 8479–8492 | gap filled (target side) | Residue values of points read on the reduced equation, multiplicatively and Frobenius-equivariantly (`read`, `read_frob`). The supersingular labels and the specialization of the operators belong to other lanes. |
| 9101–9113 | reduced to the listed inputs | (O.7) is derived in Lean from the listed inputs (`O7Actual`'s `DatumAt.representative`, `RC/O7Actual/Family.lean:111`, converts `DatumAt.reduce` into the (O.7) shape, but the actual `DatumAt` is built from `J`, `G` (now `stageRows … sp`), `relations`, `cusps` and `refs`); `oddStagedOfGoodRows` still takes `ha`, the aθ definition pin (tex 2081–2082; `RC/PMWire/Assembly.lean:221–233`), and the other `GoodRow` fields. |

## The one edit to an existing file

`docs/research/rc-model-neron.md`, the second cell of the "Same-place comparison" row of "Remaining tiers",
was replaced by the text the reviewer specified (commit `8dee6dc8f`). That edit drops Ribet's Prop. 3.3 and
Rem. 3.5 and the Cornut–Jetchev sentence.
