For a fixed realized odd-stage form and its omitted subset, `fresh_input_of_stage` and `o12_at_one_of_stage` prove the two coefficient readings with the local input named on those same vectors. The proof uses the retained precision of the odd recurrence, with the actual `ψ/η = (-1/p)` sign. `windowModel` builds the model and `O12.FourierData` from the actual theta seeds, separating the ambient Hecke exclusions from stationary Kummer support.

**Scoped stop for the global application:** `inputs_of_stage` constructs `O12.ThetaData` and applies the unchanged `O12.inputs_of_theta` on a compatible model, with its exact-lift recurrence hypothesis. `inputs_at_precision` proves the same `GaloisConstituentModel.Inputs` conclusion from the finite-stage recurrence instead. Both global applications still need a compatible realization on every tested set; the supplied finite-pool blocks realize only subsets of that pool.

## Statements

| Declaration | Statement and use |
| --- | --- |
| `tl_eq_raw` | For any enumeration without repetition of a good set, the operator product is the ordered `Lift.raw`. Supplies `H_off_unary`; list permutation bookkeeping is on-the-spot (c). |
| `hu_off_unary` | At every off-unary index, the actual integral `H_U[n]` equals `2^{-(δ+|U|+1)} TL[n]` in the coefficient field, for the chosen lifts. Take that very coefficient for `H_off_unary`; its difference from itself is zero. |
| `hu_fresh`, `fresh_input_of_stage` | At a fresh prime the divided coefficient is exactly the normalization of the actual squarefree source lift. Its residue at trace coefficient one equals the valuation symbol, using only the Hecke comparison at the tested pair. This supplies the first input pointwise. |
| `fourierF_sub_hu`, `window_theta_mod_two` | The theta convolution is `H_U[n]` plus an integer-two multiple. On an actual window seed its constituent Fourier coefficient consequently satisfies `theta_mod_two`. |
| `ratio_sign`, `signed_recur_stage` | For prime `p`, `(-1/p)` is ±1. At a good prime the two reduced lifts satisfy (O.6) with that same sign, which supplies the sign used in `C_p`. |
| `lift_depth`, `lift_source` | The truncated squarefree depth lifts from the valid stage because the exponent is at most `M`. With an exact core this supplies the integral `SourceHyp` expected by `ThetaData.source`. |
| `normalized_congr` | Agreement before division modulo `2^M` gives agreement modulo integer two after scaling by `2^{-e}` with `e < M`, if the scaled values are integral. |
| `omission_coeff_mod_two` | At `pr` with `p ∈ U` and `r ∉ U` fresh, `H_U[pr] ≡ η(p) C_p(vr) H_(U.erase p)[r] (mod 2)`. Uses stage precision and the actual divided coefficients, without an exact recurrence on their lifts. The private `tl_stage` reduces the operator product coefficientwise. |
| `phase_residue` | A two-power phase reduces to one. |
| `source_symbol_on_filter`, `source_symbol_off_support`, `stage_source_symbol` | Given the integer valuation representative and its phase comparison, the divided coefficient reduces to one exactly at the threshold. Off the filter it reduces to zero if the undivided coefficient vanishes in the stage ring. `stage_source_symbol` uses the valid-stage precision and supplies `ThetaData.source_symbol`. The helper `residue_two` sends two to zero; `residue_congr` sends congruent elements modulo integer two to equal residues. |
| `decode_one` | The additive functional on the characteristic-two residue field takes one to one. Private helpers `residue_char_two` and `exists_decode` establish characteristic two and extend evaluation on the prime subfield. The extension is on-the-spot (c). |
| `formwise_kummer` | If inertia outside the fixed support and `U) fixes the constituent trace orbits of all subsets of `U`, the stationary type and added bits detect the radical quotient. The ambient Hecke exclusions need not be in the stationary support. |
| `buildWithFormwiseInertia`, `windowModel` | Construct the constituent model and its `FourierData` from the stable lattice, integral positive coefficients and coefficient-one reading. The window specialization uses `Blocks.F`, `Blocks.coeff`, `Basis.coefK` and the existing determinant and good-operator data. The window's zero extensions carry no realization assertion. |
| `window_misses_test` | If the budget is at least two, some good singleton is tested and lies outside the pool. |
| `omission_read_of_stage`, `o12_at_one_of_stage` | The reduced trace coefficient at `p` decodes to `C_p(vr)` times the omitted form's coefficient-one reading. The same-lattice (O.12) identity then supplies the second input at this set by selecting representatives outside the ambient exclusions. Private helpers `orbitCoeff_eq_good` and `ratio_flip` evaluate a good trace at an index prime to the test prime and translate the quadratic bit flip into the opposite omission sign. |
| `thetaData`, `inputs_of_stage` | On a model carrying the actual expansions on the entire tested domain, build `ThetaData` from the same stage and apply `O12.inputs_of_theta` with `LocalInput`. For good Hecke, use `formwiseHecke_of_ambient`, whose remaining comparison is confined to primes excluded from the ambient test. |
| `inputs_at_precision` | On the same compatible model, the pointwise theorems give the original `Inputs` type with no exact integral source core or Brandt recurrence. The first reading still tests every good fresh prime; the second chooses its representatives in the ambient domain. |

## Remaining hypotheses

| Hypothesis or construction | Manuscript anchor and owner |
| --- | --- |
| Same valid stage, same good domain, budget, depth, admissibility and elliptic coefficients | Tex 9450–9455, 9471–9489, 9578–9584, 9699–9704. `Divisions`, the good-prime transfer and the equality of `a_p) identify existing Odd and theta data; App G supplies the depth and precision once the source and witness exist. |
| Actual `P_M` weights and chosen integral lifts with the stated reductions | Tex 8476–8494, 8600–8621, 9059–9082. Sibling `rc-pm`; the arguments consume `Lift` and `ThetaStage`, including its finite-precision Brandt eigenrelation. |
| Realization of the weight-two blocks, their diamond characters, and constituent attachments | Tex 9548–9555, 9620–9625, 9647–9654, 9762–9797. Existing ELLIOT realization `Blocks` and `Attachment` (with the already-used good cuspidal polynomial from Carayol). The coefficient ring and its characteristic-zero field, injective inclusion, topology, and maximal ideal over two are the chosen coefficient data of tex 9638–9666. No new print. |
| Realize the full tested domain in a compatible model | Tex 9649–9654, 9670–9679, 9919–9921. Missing integration. The smallest faithful input for the current consumer is a compatible family of form realizations on every tested set and its subsets. To use the current global model signature directly, these must give the same `FourierF` coefficients and trace readings in one model. The manuscript instead chooses a common space for a fixed set and its subsets. Reindexing the model and downstream product-label consumers around these proved pointwise identities would be a separate interface port spanning the model and both consumers; a finite pool cannot meet the current domain merely by increasing its cardinality. |
| Formwise ramification of the seed and good Hecke outside the ambient test | Tex 9660–9668, 9670–9674, 9745–9750, 9754–9769. The named `hseed` is that at `q ∉ support ∪ U), inertia fixes every constituent occurring in each seed indexed by a subset of `U`. `hexcl` is the good Fourier formula for `F_U` alone at a good `q ∉ U) excluded from the ambient Hecke tests. Missing formwise level/attachment comparisons. A formwise conductor/attachment lemma giving the relevant unramifiedness and good polynomial on the active coordinates, and the corresponding Fourier operator on their form, would suffice. The pointwise second reading does not need `hexcl` because it chooses both representatives in the ambient domain. |
| Exact core and signed recurrence of the chosen lifts; phase order | Tex 8424–8426, 9472–9476, 9585–9589, 9696–9698, 9908. The core includes exact support and character laws. The exact integral `RecAt` is an extra requirement of the current interface, not a claim of the odd-stage argument at tex 9916–9918. The route through `inputs_at_precision` already uses the finite-stage core and the proved omission congruence instead. The phase order at each good prime is the exact character comparison with the permitted two-power values; `Lift.phase` only records equality after stage reduction. |
| Valuation representative and off-filter support | Tex 2074–2086, 2522–2538, 9101–9405, 9675–9680, 9694–9704. `StageValuation` identifies the intrinsic symbol and integer representatives on the tested range, their depth and finite-precision phase comparison, and stage zero off the filter. The (O.7) comparison data and exact support are upstream ELLIOT/glue; divisibility and residue after division are proved here. |
| Two fresh traces | Tex 9705–9717, 9734–9745. The model takes `h2fresh` on the actual coefficients; sibling `rc-two-fresh`. |
| Local blocks and the bad-prime Fourier comparison | Tex 9754–9892. `LocalInput` remains on the same lattice and Fourier coordinates; siblings `rc-o12-local` (cuspidal blocks and `UpAtOne`) and `rc-o12-eisenstein` (Eisenstein blocks). |
| Stationary type | Tex 2017–2025, 9745–9750, 9932–9944. Existing `OpenTypeKernel`, `IsTypeChar`, and `TypeDetectsRadicals` comparisons with the fixed support; no detection condition is imposed on the ambient exclusions. |

The base removed `hdiam`; it is not a hypothesis of this construction or of the final conditional application. The determinant identity uses the existing coefficientwise determinant theorem. No saturation or integral projector is needed.

## Known issues

- Tex 9649, 9670–9679, 9919–9921: the manuscript uses a finite constituent space locally for a fixed stage and set, including its subsets. A bound on cardinality does not put all good sets in one finite pool. `ThetaCoeff.Blocks` is finite-pool data; `O12.ThetaData` and `Inputs` quantify over all good sets in budget. The zero extension does not identify those other Fourier expansions.
- Tex 9745–9750: the base still covers the entire ambient Hecke exclusion set by stationary Kummer support, which is incompatible with a nonempty pool by `ThetaCoeff.Blocks.pool_empty_of_stationary_cover`. The split-support construction avoids this interface error.
- Inherited source error: `ThetaCoeff/Model.lean` still passes `hdiam` to `buildConstituentModel`, whose base signature no longer accepts it. The new imports bypass that wrapper.
- Tex 9699–9704, 9916–9918: `O12.ThetaData.signed_recur` requires exact equality over the integral lifts. Equality in the stage quotient does not imply exact equality of these lifts. The first-shell result above works at the manuscript's stated precision.

## Manuscript check

- Tex 2074–2086, 2522–2538 — OK: the valuation test uses an integer representative at retained precision, not exact rationality of the lift.
- Tex 8424–8426, 9083–9093 — OK: the actual Brandt sign is `(-1/p)` at stage precision.
- Tex 9450–9455, 9471–9489 — OK: a common stage, good support and integer `δ` suffice for all the operator products in the budget.
- Tex 9486–9498, 9570–9613 — OK: order independence follows from coprimality, and the integral depth supplies the claimed integer power of two.
- Tex 9614–9636 — OK: the two divisions are divisions by integer powers of two; the omitted unary terms are zero away from their supports.
- Tex 9638–9646, 9688–9694 — gap filled: coefficient-one evaluation is extended additively from the prime subfield without identifying the abstract module quotient with reduced expansions.
- Tex 9647–9654 — unverified: the weight-two block realization and common coefficient space are supplied by the upstream realization.
- Tex 9655–9668 — OK: the closed-lattice argument uses the given integral expansions and good operators from the actual blocks.
- Tex 9670–9687 — OK: the fresh source normalization is on the same divided expansion used by the model.
- Tex 9688–9704 — OK: the integral theta correction vanishes modulo two, and the integer representative at sufficient precision gives the prime-subfield reading.
- Tex 9705–9711, 9734–9745 — unverified: the reduced two-fresh identity remains with its sibling.
- Tex 9712–9729 — OK: the existing coefficientwise determinant comparison is reused without a diamond congruence premise.
- Tex 9745–9750 — gap filled: the stationary support and the formwise inertia comparison suffice even if the ambient test excludes additional good primes.
- Tex 9754–9892 — unverified: the same-lattice local block and bad-prime Fourier data remain named inputs.
- Tex 9893–9902 — OK: the consumer uses coefficientwise reduction after evaluating the characteristic-zero identity on the integral lattice.
- Tex 9905–9918 — OK: the first-shell multiplier uses the signed recurrence modulo stage precision; both scaled coefficients are integral and agree modulo integer two.
- Tex 9919–9926 — OK: representatives for both local group elements can be chosen outside the finite ambient exclusions. Their reductions agree on the two realized forms and the retained bits give opposite omission signs.

## Verification

All ten new Lean files compiled with `lake env lean -j1`, one at a time. All 37 declaration audits reported only `propext`, `Classical.choice`, and `Quot.sound`. No new printed-form leaves were added.
