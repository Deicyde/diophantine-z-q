# rc-model-target: hand-off

**Main result.** The good integral Weierstrass cubic now supplies every target-side field of
`PMWire.GoodRow`, with no leaf. Take `R = ℤ_(ℓ)` with `5 ≤ ℓ`, and `W₀ : WeierstrassCurve ℤ` with `¬ ℓ ∣ Δ(W₀)`,
carried as detector data; the frozen route has `W₀ = EcurveZ ℓ` with `¬ p ∣ Δ` from
`StageWitness.stage_facts`. Then `E = weierstrassModel ℓ (W₀.map (ℤ → R))` is:

* smooth (`weierstrassModel_smooth`);
* a group object (`weierstrassModelGrp`, glued from Mathlib's `addXYZ` and Tau Ceti's Bosma–Lenstra `dblAddXYZ`);
* a Néron model (`weierstrassModel_isNeron`).

The supplied fields:

* `jE`: `cubicJE` / `detGenericIso`, the identity in coordinates via the general `bcIso`;
* `properGenericE`, `geomIntGenericE`;
* `readComplex`, `readComplex_eq`: `readComplexCubic`, with `rfl` against `projectiveValue`;
* `read`, `read_frob`: the actual reduction of the points of `W` onto `ReducedEquation W₀ ℓ ⁄ K`.

`goodTarget` packages these fields, and `GoodTarget.toGoodRow` builds a `GoodRow` from them plus the other
lanes' fields. The `LocalTarget` route is also filled: `NeronDVRLocal` enters only as the proved closed term
`neronDVRLocal`, with `neronLaw` and `localReadComplex`.

**Retired frozen field or GLUE row:** none yet. The `hRC` row (`docs/one-proof/OPEN.md:462`) and
`PreLeaves.odd_staged` (`RC/Wiring/Leaves.lean:305`) still need `point`, `point_frob` and `frobenius_sq`
(same-place lane), `point_W` (an input of `SamePlaceData`, same-place lane in the hCM lane; it also needs the
special-fibre action of `Wint`, generic5 item 4, not started), and `ha`, the aθ definition pin
(tex 2081–2082; `RC/PMWire/Assembly.lean:221–233`, consumed at `RC/O7Actual/Family.lean:121`); (O.7)
is derived in Lean from the listed inputs (`O7Actual`'s `DatumAt.representative`, `RC/O7Actual/Family.lean:111`, converts `DatumAt.reduce` into the (O.7) shape, but the actual `DatumAt` is built from `J`, `G` (now `stageRows … sp`), `relations`, `cusps` and `refs`). The other inputs of `oddStagedOfGoodRows` (`refs`, `J`,
`relations`, `cusps`, `hL`, `hsign`) are also still open. `extension` is supplied by `ModelGeneric5.goodRow_extension` (witness `Wint`).

**What compiles.** 24 new modules under `ZInQKernel/Contrib/OneProof/RC/ModelTarget/` build with
`lake build`, with no `sorry` and no axiom declaration. `#print axioms` gives only propext, Classical.choice
and Quot.sound. The modules:

* ComplexReading, LocalReading;
* ChartRing, ChartPresentation, ChartSmooth, ChartSmoothY, WeierstrassSmooth;
* ChartMorphism, FieldValue, FormulaGluing, FormulaMorphism, RuleGluing, GroupLaw, GroupObj;
* BaseChange, BaseChangeInv, BaseChangeIso, DetectorModel;
* PullbackMul, Read, ReadEquiv, CubicComplex, Supply.

**Leaves used:** none.

**Required edit:** item 6, the same-place row of `docs/research/rc-model-neron.md`, is done (commit `8dee6dc8f`).

**What remains in or near this lane:**

* `LocalTarget.E ≅ E` (optional; Néron uniqueness both ways);
* rebinding `isReduced_of_smooth_hom`, which uses a vendored proved FLT-port theorem from a CloudR2NOS
  staging copy; it is four lines over Mathlib.

Report: `docs/research/rc-model-target.md`. Log: `scratch/rc-model-target/log.md`.

**SHAs.** Last Lean commit: `840b43927e5a35eabf61129460410627c2c90fb0`. Hand-off commit with the report: `292a97a5a01c0807fb5017ac8bba5caf0d2534c1`. This file is committed last, on top of these.
