# Appendix F: actual evaluations at the genus data

The detecting sequence gives an actual `StageKummer` at every conductor-one genus
datum on the moving Legendre support. At stage `θ`, reduce at the restriction of
the absolute place already used for the witness, apply the square-Frobenius Kummer
map at precision `Mθ θ`, and apply the fixed row on finite torsion. The selected
witness entry is exactly `actualStageMapOn`, giving `hev`,
`WitnessSpecialization`, and (O.2) for this same total map. For every admissible
pair with `selG D = some t`, including every such nonwitness pair,
`lamOf_admissible` gives the integer lift of that evaluation on `L • genusPoint t`.

The scope stops at the existing genus selection and the theta comparison. In
particular, `selG` in the base interface can be `none` at an admissible parameter
that is not a known simple zero. The manuscript uses a genuine point there as
well. The stage map is defined for every datum on the support, regardless of
selection or analytic rank. To read it on an actual genus point at every
admissible pair, the assembly must choose a datum at each such parameter.

## Statements and consumers

Paths are relative to `ZInQKernel/Contrib/OneProof/RC/StageMap/`.

| Declaration | Statement and consumer |
| --- | --- |
| `Actual.lean`: `anchoredEmbeddings_witness` | The chosen embedding of the witness datum is exactly the one in `ExactWitnessOn`. Used by `hev`. |
| `Actual.lean`: `Evaluations.ev_of_support` | For every datum `t` on the stage support, `ev θ D t = (eval θ).comp (reduction θ D t h)` as additive maps. Supplies the pointwise `ev` for arbitrary inputs, including the Heegner conjugates used in `Visibility.lamOf_reduction`. |
| `Actual.lean`: `Evaluations.lamOf_eq` | If `selG D = some t` and the pair is on support, `lamOf` is `Int.ofNat` of the canonical `ZMod` representative of `eval θ (reduction θ D t h (L • genusPoint t))`. Supplies the comparison reading before specializing to `WData`. |
| `Actual.lean`: `stage_disc_of_test` | For every datum of `D` passing the moving test, the stage prime does not divide its discriminant and the discriminant has Legendre symbol `−1` there. Supplies unramified inert descent for `ev`. |
| `Actual.lean`: `ringClassRed_agrees` | After embedding the quadratic residue group in the absolute residue curve, the descended reduction of any point equals geometric reduction after embedding the point in the absolute closure. Supplies the precise place of the pointwise `ev`. |
| `Actual.lean`: `actualEvaluations_at_witness` | On the curve of the integral model at its original precision, the new `ev θ Dw dat` equals the old `actualStageMap θ Dw dat` as additive maps. |
| `Actual.lean`: `actualEvaluationsOn_at_witness` | The same equality with `actualStageMapOn`, transported to the model and stage precision of the instance. Supplies `hev`. |
| `Actual.lean`: `actualEvaluationsOn_spec` | For the fixed witness division tower the new stage map satisfies `WitnessSpecialization` by `witnessSpecialization_of_agree`. Supplies the finite identity used in (O.2). |
| `Consumers.lean`: `actualForStages_at_witness` | The `hev` equality for `actualForStages.ev` on `Ecurve ℓ` and `W.Mθ`. |
| `Consumers.lean`: `admissible_stageTest` | If `withStages W q W.prepared = W` (from `StagesFrom.withStages_eq`), then `W.admissible θ D` implies `stageTest q θ D`. Thus the comparison never reads the off-support extension. |
| `Consumers.lean`: `lamOf_admissible` | For the transported actual evaluations on `Ecurve ℓ`, an admissible pair and a selected datum give the canonical integer lift of `b(κ_{Mθ θ}(reduction(L • P_D)))`. Supplies the `lamOf` argument of `hcore`; no rank or `D ≠ Dw` hypothesis is needed. |
| `Consumers.lean`: `witnessValuation_actualForStages` | With the fixed detector value and the prepared and selected witness, (O.2) holds for `actualForStages.ev`: the witness is admissible with valuation `a + 1` in the stage filter (the existing witness theorem gives the assertion at each stage). |

Use `actualForStages … .ev` as `OddModels.ev`, with
`actualForStages_at_witness` for `hev`. In both cases pass
`hstages.withStages_eq` from the existing stage data. The fixed group in
`actualEvaluations` is that of the square of arithmetic Frobenius. For an input
in that group, `reducedRead` uses `κ(P) = F² R − R` for `2^M • R = P`, then
the inverse prime-to-residue-characteristic torsion specialization (through
the split witness twist), then `finiteRow b M`. The ring class reduction varies
with the datum; the finite read is the same for all data at the stage.

The use of principal ideal reciprocity to supply the quadratic residue and
the comparison of finite and absolute reductions are the on-the-spot (c)
steps already proved in `RC/WitnessSpec`. Simultaneous field embedding choices,
the transport along the integral model and precision, and the integer lift
through the optional selection are on-the-spot (c) in this lane.

## Remaining hypotheses and interfaces

| Input | Manuscript | Owner and status |
| --- | --- | --- |
| Existing witness datum, `ExactWitnessOn` (including `L` and the exact twist equality), its integral model, actual sequence `q`, square Tate action `hσ`, and fixed row `b`; for the instance, `StagesFrom`. For the valuation also `hQw`, Galois fixedness of `Q`, its division tower, the exact row value `2^(a+1)`, witness preparation and selection. | 2460–2498, 8295–8316, 8340–8405, 10190–10191 | Existing witness and stage construction, carried as its outputs. No new arithmetic hypothesis about other primes, Kummer maps or data. |
| Chosen embeddings of the datum fields into the same absolute closure (the witness datum uses `w.emb`). | 2497, 8362–8366, 9265–9274 | Choices, provided by `chooseDatumEmbeddings` if the comparison does not already specify them. The comparison has to use those same choices. |
| For the geometric reading at every admissible nonwitness pair: `∀ θ D, W.admissible θ D → D ≠ Dw → (selG D).isSome`. For a prescribed comparison datum the exact local hypothesis is `selG D = some t`. | 8209–8219, 9105–9113, 9272–9291, 9439–9443 | Missing genus selection in the shared interface. If genuine data are supplied, filling missing choices is small. Proving their existence from the prepared filter alone is larger: the minimum is `Nonempty (HeegnerDatum E f Lat κ (D*hstar) 1 hstar)` for each uncovered parameter, including the Heegner form and the algebraic realization of its parametrization value. The existing CST print is a height identity for a supplied point and does not provide this existence. With the choices made, `lamOf_admissible` reads every comparison parameter. No additional leaf was added. |
| Identification of the reference Heegner point and its conjugates with the supersingular values at this same reduction; the oriented count, theta coefficients and phase, and `hcore` / (O.7). | 8476, 9104–9117, 9257–9294 | ELLIOT comparison input, with theta-side sibling work. Feed the pointwise `ev` equation to the existing `Visibility.lamOf_reduction` once its pointwise Cornut–Jetchev hypotheses are supplied. |

## Known issues

- The base `GenusOddInstance.hselG` guarantees a selection only at prepared simple zeros.
  `lamOf` takes its existing default of zero at `none`; this is not a construction
  of a reduced genus point. No comparison hypothesis is used to infer selection.
- When `(D/p)` is zero or negative, the manuscript uses the off-support
  coefficient statement instead of the comparison formula. The stage map has
  a zero extension there solely to inhabit the total `StageKummer` type. There
  is no assertion that those ring class fields have quadratic residue at the
  chosen prime or that their geometric points evaluate to zero.
- No manuscript or source error was found in the steps used here. The cited
  Cornut–Jetchev source and its external locators were not independently checked;
  the new proofs use the existing geometric reduction and class field results
  rather than the printed embedding count.

## Manuscript check

- 2404–2416, 8209–8219 — OK: use the conductor-one unaveraged genus point for each supplied datum, distinct from the companion point.
- 2460–2498, 8340–8377 — OK: keep the fixed witness, multiplier, detector row, and chosen Frobenius place at each precision.
- 8378–8398, 8439–8456 — OK: reuse squared arithmetic Frobenius and inverse torsion specialization for the finite read and the exact witness identity.
- 9205–9209 — OK: the split test on `D` times the nonsplit sign on `h_*` gives the unramified inert sign on the datum discriminant.
- 9288–9290 — gap filled: at the restricted place the inert base prime is principal, so conductor-one reciprocity gives quadratic residue; the same local map applies to the whole ring class point group.
- 9265–9272 — gap filled for the elliptic-curve side: finite reduction at the contracted place agrees with absolute reduction at the witness's place; the Cornut–Jetchev identification on `X₀(N)` belongs to the comparison.
- 2522–2535, 9105–9113, 9283–9291 — OK for the geometric argument of `λ`: use the finite composite on `L P_D` on the split support and take its canonical representative for `lamOf`.
- 9272–9277, 9439–9443 — unverified for an arbitrary output of the current selector: the manuscript uses the reference point even off simple zeros; the Lean implementation has no all-admissible selection guarantee.
- 2522–2535, 9104–9117, 9266–9291 — unverified for (O.7): the geometric-to-theta identification and weighted count are outside this lane.
- 2490–2493, 2534–2536, 8392–8398 — OK: the total map has the unchanged exact witness specialization and detection valuation.

Both Lean files were checked separately with `lake env lean -j1` in a local
build overlay. All twelve theorem audits report only `propext`,
`Classical.choice`, and `Quot.sound`.
