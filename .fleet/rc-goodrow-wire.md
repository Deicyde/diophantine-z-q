# rc-goodrow-wire hand-off

**Retired frozen field:** none yet. The `hRC` GLUE row (`docs/one-proof/OPEN.md`, section `hRC`) and
`PreLeaves.odd_staged` (`RC/Wiring/Leaves.lean:305`) are unchanged until `sp` and the other remaining
inputs are supplied.

**Error verdicts:** none.

**Main result.** `GoodRowWire.oddStagedOfSamePlace` (`RC/GoodRowWire/Assembly.lean`) is
`PMWire.oddStagedOfGoodRows` with `G` and `hcop` replaced. `stageRow` (`RC/GoodRowWire/Row.lean`)
assembles `PMWire.GoodRow` at every stage prime from:

* the pinned model `Pinned.Y0Level` and `ModelNeron.source` (levels and neron lanes);
* the good cubic `ModelTarget.goodTarget` with `W₀ := EcurveZ ℓ` and `hΔ := StageKummer.goodAt s i`
  (target lane);
* `ModelGeneric5.goodRow_extension`, with witness `Wint` (generic5 lane);
* one explicit input, `SamePlaceData` (`RC/GoodRowWire/SamePlace.lean`), which holds `point`, `point_W`
  (stated with `Wint`), `point_frob` and `frobenius_sq`. Its owner is the same-place lane in the hCM
  lane (tex 8479–8492). It fixes `point` only up to an equivariant choice on each orbit, and faithfulness
  is carried by `refs` and `relations` over the same `stageRows … sp`, so `sp`, `refs` and `relations`
  must come from one construction of `point` (report, Known issues). `X.frobenius` is pinned on `X.ss`
  by `O.frobenius` (ELLIOT; `RC/PMAdelic/Comparison.lean:103–104`), read through `J.classes` (GLUE).

All type equalities hold by definitional unfolding, so no bridge or cast was needed.

**Accounting.** G and hcop are replaced by hB and sp; hcop and htame are derived from hB
(`GoodRowWire.stage_coprime`, `ModelGeneric5.stagePrime_not_dvd_tame`); h2 comes from `two_le_level hN`.
h5 comes from `stagePrime_five_le s i`. `J`, `O`, `relations`, `cusps`, `refs` and `ha` are restated with the
same content under the substitution `G := stageRows a s π hQ hN hB sp`,
`hcop := stage_coprime s hN hB` and `R i := LocalIntegers (s.q.stage i).p`. No free `G`, `hcop` or `R`
is left.

**What compiles.** `RC/GoodRowWire/{SamePlace,Row,Assembly}.lean` build with `lake build`, with no
`sorry` and no axiom declaration. `#print axioms` of every new declaration gives only propext,
Classical.choice and Quot.sound. The item-1 doc fixes to the target and neron reports are committed
(67896e640).

**What remains.**

* `sp` per stage, from the same-place lane. `point_W` also needs the special-fibre action of `Wint`
  (generic5 item 4, not started).
* `hB`, from the stage lane. It is satisfiable by choosing `B' ⊇ (N φ(N)).primeFactors` in
  `exists_detector_stages` (`subset_stageExclusions`).
* `J`, `O` (`PMAdelic.OperatorComparison`, ELLIOT) and `refs` (hCM lane), `relations` (detector specialization), `cusps` (J0Cusps), `H` and `hm`,
  `ha` (aθ pin, tex 2081–2082), `hL` and `hsign`. These are unchanged in content.
* `π`, `hQ` and `han` (the fixed parametrization and its complex reading `phiAn`; `han` is a
  substantive input), `F` and `hN`, and the three instance arguments (`NeZero` of the newform level
  and of `StageKummer.level ℓ`, and `IsElliptic` of `(EcurveZ ℓ)⁄ℚ`), as in `oddStagedOfGoodRows`.
* `X`, the coarse fibres: fixed by `J`'s owner (hCM lane); `sp` must be supplied for the same `X`.

Report: `docs/research/rc-goodrow-wire.md`. Log: `scratch/rc-goodrow-wire/log.md`.

**SHA.** Last Lean/report commit: bcfebfc57; this hand-off file is committed on top of it (the branch tip is the final SHA).
