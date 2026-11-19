The selected Appendix F theta stage and the skeleton now use one prime, precision, order level, detector, extracted index and intrinsic filter. `inputs_of_selected` applies the existing finite precision (O.12) consumer with this data. It supplies both Fourier support comparisons and chooses the operator budget `W = B - 1` and truncation `R = 2` for output sizes at most `B`. It still takes the actual local and adelic geometry, (O.7), the exact sieve, a valid App G depth certificate, and the (O.12) constituent data. In particular, the selection of a valid stage is not an output of this lane.

## Known issues

- Inherited interface error if the address filter is used as the intrinsic Fourier filter: `W.admissible` can veto additional primes, so equality against it on all squarefree indices is unwarranted. Tex 2026–2029 and 9481–9483 explicitly disallow such a resieve. The new label constructor proves compatibility with `W.admissible` only on indices avoiding the enlarged support; its intrinsic filter is constructed separately. An arbitrary old `LabelData.oddAdmissible` only has that restricted compatibility. Its fixed modulus data can be reused to construct the selected labels; the unrestricted equality is for these selected labels.
- Inherited terminology at `ZInQKernel/Contrib/OneProof/RC/AppF/Stage.lean`: the actual extracted series retains its phase. The integers in `W.aθ` are the phase-removed valuation representatives; (O.7) compares the two.
- At genus parameters where `selG` is absent, the base tree's `lamOf` defaults to zero, even though the manuscript uses an actual genus point there. The detector equality is on the entire quadratic residue point group and the total stage-map constructor is defined on every supplied datum. It does not establish the missing genus data. See `docs/research/rc-stage-map.md`.
- The raw `PMLocal` fields allow extra exclusions and do not specify `m = |h_*|`, or certify which fixed sieve primes contribute to the intrinsic type modulus. These are construction data, recorded directly against `F.m` and `F.support`. The local support fields alone only force the primes of 2mNℓ₀ into that set. Tex 1974–1975 and 8247–8258 separately specify the fixed support containing 2, 3, and the bad primes, corresponding to `LabelData.bad₁`. No new print or external locator from memory is used.

## Statements and consumers

Names below are relative to `ZInQ.Manuscript.RC.StageIdent`. Let `pᵢ = (q.stage i).p`, `N = CST.newformLevel (Ecurve ℓ)`, `m = |h_*|`, and `Sfix = Q.m₁.primeFactors`, where `Q.m₁` is the fixed intrinsic odd modulus. The selected labels have type conductor `Q.m₁ * pᵢ`. The fixed unit tests are the ones supplied in the prepared filter; the finite coefficient exclusions may also include primes required only for zero-or-retain sieving.

| Declaration | Statement and use in `inputs_of_pm` |
| --- | --- |
| `reducedEquation_elliptic` | Reducing an integral Weierstrass equation away from its discriminant gives an elliptic equation. Supplies the reduced-curve instance in `G` and `d`. |
| `finiteRow_fixed_of_agree` | If `b ∘ ρ(σ) = b` on the Tate module and `g` agrees with σ on the finite torsion field, the finite row `finiteRow b M` is fixed by `g` on the level torsion. Supplies the Frobenius invariance of `d`. |
| `selectedCurve_elliptic`, `selectedCurveOn_elliptic` | The reduced equation is elliptic at pᵢ, by the actual stage's good reduction. The second statement transports the integral generic fibre and exact rational witness. Supplies the curve instance at the selected stage. |
| `selectedEvaluation_lam` | In the integral presentation, `PM.lam selectedEvaluation` is the same additive map as `StageMap.actualEvaluations.eval i`: square-Frobenius Kummer followed by the finite row composed with inverse torsion specialization. Supplies the identity of the detector in `d`. |
| `selectedEvaluationOn_lam`, `detectorAt_lam` | The same equality after transport along the generic fibre, witness and precision; the latter names `StageMap.actualForStages.eval i` directly. The carriers of the quadratic fixed groups are dependent projections, so the transported identity is expressed by `HEq`. Supplies the same `d` at `W.Mθ i`, for all points. |
| `level_eq` | The newform level of the integral model's generic fibre equals the skeleton curve's newform level. The geometry is indexed by that level. |
| `pmStage_parameters` | `G.eichler` is `IsEichler pᵢ N R`; the built theta stage has `ℓ₀ = pᵢ` and `m = W.hstar.natAbs` when the local constructor uses `F.m = W.hstar.natAbs`. Supplies the geometry and index identification for the `pmStage G d L F` used by `inputs_of_pm`. |
| `pmStage_weight` | The stage class weight is the stage-ring image of the selected detector applied to `L • G.pi z`. This is the actual `P_M` in the weighted series fed to `inputs_of_pm`. |
| `stageTest_not_dvd` | The moving Legendre condition `+1` implies `pᵢ ∤ D`. Used in equality of the predicates indexing `C`, `depth`, `off` and the model. |
| `labelsAtStages_prime_precision` | The selected `LabelData.ℓ₀ i` is pᵢ, and `W.Mθ i = cw + 1 + i`. Identifies the type conductor and the precision of `d` and `F`. |
| `sourceFilter_eq` | If `support = insert pᵢ Q.m₁.primeFactors`, the full source predicate on all integers equals the selected intrinsic predicate: positive squarefree, prescribed fixed unit-square tests, avoidance of `Sfix`, and the moving Legendre test. Supplies the common domain of `C`, `depth`, `off` and the model. |
| `pmLocal_base_support` | Every prime dividing `2 * F.m * N * ℓ₀` belongs to `F.support`, by `neTwo`, `goodM` and `away`. Records the local constructor's original coverage; its fixed support can be larger. |
| `bad_mem_support` | For a prime `p ∣ 6ℓ`, `LabelData.bad₁` puts `p` in `Sfix`, hence in `F.support` under the displayed support identity. Supplies `hbad`. |
| `support_dvd_type` | Every member of `F.support`, under that same identity, divides `Q.m₁ * pᵢ`. Supplies `hcover`, so type-good primes are good for the Fourier source. |
| `rodd_atStage` | The selected labels' `Rodd` equals the valuation's `intrinsic` on every finite set of primes, on the full source filter and with the same `W.aθ i` and `W.δo`. Identifies the reading in the model index. |
| `reading_budget` | For every `B : ℕ`, `B ≤ (B - 1) + 1` and `2 ≤ 2`. Supplies `hbudget` and `hR`; App G's precision inequality is still in `IntegerDepth`. The `B = 0` case also satisfies the consumer's budget condition. |
| `inputs_of_selected` | On the chosen theta series with its least lift of (P_M), the selected order/prime/index and full filter identities hold, and `X.Inputs` follows by `inputs_of_pm`. The comparison, depth and exact support inputs are on this one source. |

`sourceFilter`, `labelsAtStages`, `selectedEvaluation`, `selectedEvaluationOn` and `detectorAt` construct data. No new structure or proposition is taken as a hypothesis. The pointwise predicate `sourceFilter` is built from the manuscript's unit, avoidance and split tests; it has no valuation, vanishing, depth or (O.12) field. The identities for the level, prime and detector use the indices and the arithmetic already on the stage. The two raw field identities `F.m = |h_*|` and `F.support = insert pᵢ Sfix` describe the parameters of the local construction, not vanishing or comparison of Fourier coefficients. In particular the support identity permits all prescribed fixed sieve primes, not just the original level and discriminant primes. Replacing the label fields, transferring the fixed row and coordinating the dependent precision and support types are on-the-spot (c).

## Remaining hypotheses

The following is the full boundary of the application; the last four rows are existing (O.12) model inputs, separate from the selected stage.

| Input still needed | Tex | Owner and size |
| --- | --- | --- |
| Selected stage and fixed parameters: `q, i`, the exact witness and multiplier, `hσ`, the fixed row and its invariance under σ; `withStages W q W.prepared = W`; label moduli, the prepared unit tests, and their fixed prime inclusions in the sequence's exclusion set and the address support. | 2460–2498, 8247–8258, 8340–8405, 10190–10199, 10589–10596 | Existing detecting sequence and wiring, and selected labels. The stage selector lane supplies a valid index; this theorem works for a given one. Use `StagesFrom.withStages_eq`; `StageSupport.prepared_eq` supplies the shape of the prepared filter. A new field prescription after selecting the sequence is not justified by this inclusion. |
| `G : PM.Geometry` at `pᵢ, N, Ecurve ℓ mod pᵢ`, with the given order `R`, class identification and specialization of the modular parametrization, and the Hecke, Atkin–Lehner and uniformizer identities on it. | 8462–8494, 9039–9042, 9276–9291, 9331–9358 | Adelic level structures: `pm-adelic-join`; actual supersingular/modular parametrization geometry: existing ELLIOT input `PM.Geometry`. The minimum is the geometry of this one order, not a new global theory of all levels. The detector is constructed here; no separate `PM.Evaluation` hypothesis remains. |
| `F : PMLocal` on that `R, M, N, pᵢ`, with `F.m = W.hstar.natAbs` and `F.support = insert pᵢ Q.m₁.primeFactors`. If `Q.m₁` is supplied independently, its prime factors must be the fixed coefficient exclusions (including any actual late sieves). | 8209–8212, 8410–8428, 8495–8576, 8600–8621, 9045–9093, 9471–9483 | `rc-theta-join`: actual integral local weights, character and three frame comparisons, with these two parameter choices. The base support at 2mNℓ₀ and the good-prime consequences are proved here. |
| `O7Comparison` on the exact weighted source and same `W.aθ i`. This includes the actual genus data needed at admissible parameters and comparison of their reduced points with the oriented supersingular class sum; `actualForStages` supplies their finite evaluations. | 2522–2538, 9101–9405, 9675–9680, 9694–9704 | ELLIOT input. Minimal statement is the stage equality with permitted phase for each admitted squarefree index, using the same representative. The construction of genus data at parameters where the base selector gives none remains missing as described in the stage-map report. |
| `sieve` and `off`: zero for integral coefficients at each index divisible by a Fourier support prime, and stage zero at every squarefree index outside the full intrinsic filter. | 2530–2532, 8495–8566, 9092–9098, 9471–9483 | Exact Fourier sieve and local Schwartz support (ELLIOT input). Two pointwise vanishing claims on the actual source. |
| `IntegerDepth` at `i`, for `W = B - 1, R = 2`, with `W.δo` the minimum on the intrinsic filter. | 9385–9445, 9450–9455, 9578–9584, 10175–10252 | `rc-appg-coarse` for (F.5); existing stage validity and minimum input for the attained minimum on this filter. The existing `integerDepth_of_data` yields the eventual certificates from those premises and advancing precision; `rc-stage-selector` chooses the common valid stage. |
| Compatible (X), `A`, `hm`, `hexp`: one constituent model at the same coefficient place, with the domain and characteristic-zero instances, maximality, and Fourier equality including the constant coefficient for every tested (U) and its subsets. | 9638–9668, 9670–9679, 9762–9797, 9919–9921 | `rc-o12-realize` and ELLIOT Fourier comparison. The current interface ranges over all tested sets at bounded cardinality; a finite prime pool does not suffice. |
| `htyp`, `ops`, `DF`, `hDF`, `A.FormwiseHecke`, and stationary quotient and two-fresh data already in (X). | 9660–9668, 9688–9694, 9705–9750, 9919–9944 | ELLIOT stationary type input and existing `rc-o12-formwise` and `rc-two-fresh` lanes, on the same model. |
| Cuspidal part of `LocalInput A`: local identities for the tests on each pair and the resulting coefficient-one comparison. | 9754–9853 | `rc-blocks-per-u`, with the existing local block interface. |
| Eisenstein part of `LocalInput A`: local alternatives and coefficient-one comparison on the same lattice. | 9854–9892 | `rc-eis-form`, with the existing local block interface. |

## Manuscript check

- Tex 1974–1975, 8247–8258 — OK: the fixed unit filter already includes 2, 3 and the bad primes, and is enlarged before the fixed witness.
- Tex 2016–2029, 9471–9483 — gap filled (c): build separate intrinsic and address filters, and compare only on indices avoiding the enlarged address support.
- Tex 2074–2086, 10236–10252 — gap filled (c): the actual full filter and the valuation predicate agree on all integers; the existing threshold reading then agrees on prime products.
- Tex 2489–2497, 8399–8405 — OK: the selected prime, place and stage precision come from one sequence; the fixed label avoidance is passed to that sequence.
- Tex 8209–8212, 8410–8418 — OK: the local extraction uses `m = |h_*|`, with a positive squarefree parameter in the prescribed unit classes.
- Tex 8432–8459 — gap filled (c): specialize the fixed finite row at the actual place and transport its equality with the genus evaluation to the skeleton's precision.
- Tex 8462–8479 — unverified: the application uses the supplied adelic and supersingular geometry for the same curve, prime and order level; no new existence claim is proved.
- Tex 8495–8566, 9471–9478 — gap filled (c): fixed exclusions and the current reduction prime give the type conductor divisibility and coverage over 6ℓ; the exact coefficient zeros remain inputs.
- Tex 9045–9093 — unverified: the existing Brandt recurrence consumes the actual local frames supplied in `PMLocal`.
- Tex 9101–9405 — unverified: the phase and point comparison (O.7) is an input on this same source.
- Tex 9450–9455, 9578–9584, 10208–10252 — OK: an output bound `B` permits an operator bound `B - 1` and truncation 2 at a valid stage; the depth bound is still an App G certificate.
- Tex 9638–9944 — unverified: the Fourier/model comparisons and local inputs to the unchanged (O.12) consumer are explicit premises.

## Verification

`Detector.lean`, `Filter.lean` and `Apply.lean` compiled individually with
`lake env lean -j1`, with the devserver load and available memory checked before
each invocation. The 23 audits, including every new theorem, reported only
`propext`, `Classical.choice` and `Quot.sound`. No new printed-form leaves.
