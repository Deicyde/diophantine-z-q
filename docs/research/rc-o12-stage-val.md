`inputs_of_pm` applies `inputs_at_precision` to the actual weighted odd source at one valid stage. The odd and theta calculations share the same weighted theta series, precise finite stage, integer depth, admissible sets and elliptic coefficients. The result gives the original two (O.12) inputs on a compatible constituent model. It is conditional on (O.7) and exact support, the actual geometry and local frame data, and the remaining model comparisons listed below.

The valuation uses the full intrinsic odd filter and the skeleton's phase-removed integers. At a tested product of distinct good primes, App G supplies the full threshold bound and precision strictly above that threshold. The existing source supplies zero off the filter; the named (O.7) comparison supplies the stage equality with the integer representative times a permitted phase on the filter.

## Known issues

- Source interface error if the address filter is used for the Fourier support: the tree's address assembly explicitly allows `RCData.admissible` to impose later exclusions that `LabelData.oddAdmissible` does not impose. The filters are compared on primes avoiding the enlarged support; that does not give theta coefficient vanishing at every squarefree index vetoed by the address filter. Tex 2026–2029 and 9471–9483 expressly rule out such a resieve. Use the full intrinsic odd filter for (O.7), App G's minimum, and `Divisions`; transfer only the good-prime tests.
- Source terminology: comments in `RC/AppF/Stage.lean` call `aθ(n) = H(mn)` phase removed. (O.7) retains its phase; it is the integer representative in the valuation test that has the phase removed.

- The finite-pool realization from the upstream theta task does not realize the global tested domain. Its zero extension does not supply `hexp` on other good sets.
- The exact-lift recurrence of the other `ThetaData` interface is stronger than tex 9699–9704 and 9916–9918. This application uses the unchanged finite-precision consumer.

## Statements

All names are in `ZInQ.Manuscript.RC.O12StageVal`. Let `n(V) = ∏ p ∈ V, p`, let `a` be the phase-removed integer representative, and let `T₀ = max(0, δ + W) + R`. Statements about tested sets use good primes and cardinality at most `B ≤ W + 1`.

| Declaration | Statement and consumer |
| --- | --- |
| `inner` | The ternary coefficient at a class and index is the sum of the integral local weights over the trace-zero reduced norm sphere. Both sides of `Lift.localSum` use this sum. |
| `pmStage` | On the class set of the given order, the existing `PM.appFStage` uses the reductions of the integral norm character, ternary coefficients and characters, and uses the image of `P_M`. Its good domain is exactly the primes outside the coefficient support and its `ap` is the function in the geometric input. |
| `pmLift`, `pmValLift` | Associate to any chosen integer lift of `P_M` (in particular the least representatives) the integral `Lift` of that stage. The classes and masses agree, as do the reduced weights, norm character, local sum and character. Existing `Lift.aθ_reduce` then gives coefficientwise reduction. |
| `pmLift_zero` | If the integral local ternary coefficient at zero vanishes in every class, so does the lifted extracted coefficient. Supplies `Divisions.zero`. |
| `pmLift_recur` | The chosen lifts satisfy `RecAt` after reduction modulo `2^M`, with elliptic eigenvalue `a_p` and ratio `(-1/p)`. The finite Brandt identity uses `PM.P_hecke` on the same weights; it supplies the recurrence used by the divisions and the omission reading. |
| `PMLocal.eta_order` | On the good domain, the integral `η = s · χ_{h_*}` has two-power order because `s` does and the quadratic value is a sign. Supplies `hphase`. |
| `integerDepth_of_min`, `integerDepth_of_witness` | From (F.5), advancing precision, and the attained minimum (or the fixed visible witness that constructs it), App G eventually gives `T₀ ≤ M` and `min(T₀, δ + ω(n)) ≤ v₂ a(n)` on the squarefree intrinsic filter, for each fixed budget. Supplies `IntegerDepth` for the selected stage. |
| `integerDepth_of_data` | The same choice for `RCData.Mθ`, `RCData.aθ` and `RCData.δo` when that depth is the minimum on the full intrinsic filter. |
| `o7Comparison_of_core` | The existing `ComparisonCore.O7` with a prescribed two-power phase gives stage equality with the phase times the integer `c₀ · 2^ω(N) · lam(n)` for that very lift. Supplies `O7Comparison`. Other representatives can be supplied via the same named stage equality. |
| `divisions` | Assemble `Divisions` from the App F source, (O.7) on that source, `IntegerDepth`, the good mod-four congruence and the two support premises. Depth maps to stage divisibility. The stage source uses the finite Brandt recurrence. |
| `prime_index` | The product of a finite set of primes is squarefree and has exactly as many distinct prime factors as the set has elements. Supplies the index in both the depth and support comparisons. |
| `intrinsic`, `intrinsic_read` | Evaluate `Symbols.coeffSymbol` on the product of the primes, using the integer representative in `ℚ₂`. Its test is exactly membership of the intrinsic filter and `v₂ a(n(V)) = δ + |V|`. Supplies the reading field of `StageValuation`. |
| `threshold_congr` | For `e < M`, the test `v₂ a = e` is unchanged by adding an integer multiple of `2^M` to the phase-removed representative. |
| `tested_depth` | For a tested set the exponent `δ + |V|` is strictly below `M` and is a full integer lower bound on the filter. Supplies the depth in `StageValuation.onFilter`. |
| `good_of_support`, `admissible_of_good` | A type-good prime avoids the actual Fourier support if each prime of that support divides the type conductor; a tested operator set then meets the stage's `Admissible` predicate in the same budget. No converse is required for additional label exclusions. |
| `stageValuation` | Package the intrinsic reading and integer representatives, their lower bound and phase comparison, and stage zero off the squarefree filter from `Divisions.stage`. Supplies `valuation`. |
| `rodd_eq_intrinsic` | On prime sets the address assembly's `Rodd` has the same values as the intrinsic symbol, using `LabelData.oddAdmissible` and the skeleton's integers. |
| `pmDivisions` | Specialize `divisions` to the actual weighted lift with elliptic coefficients `apo ℓ`. At primes outside the Fourier support use the tree's mod-four curve theorem, with the primes over `6ℓ` in the support. |
| `inputs_of_pm` | On the model indexed by the actual intrinsic reading and `apo ℓ`, apply `inputs_at_precision` to that weighted lift, the resulting divisions and `StageValuation`. The coefficient equality `hap` is reflexive; the good transfer, phase order, and budget are on this same source. |

## Remaining hypotheses

The application takes a chosen index of the actual stage family. The last column assigns each remaining input, including prerequisites of the named records.

| Remaining hypothesis | Tex | Owner and smallest required comparison |
| --- | --- | --- |
| The actual supersingular geometry and detector | 8358–8395, 8439–8494, 9039–9042, 9278–9291, 9331–9358 | Existing ELLIOT inputs `PM.Geometry` and `PM.Evaluation`: the order, specialization, neighbour identities, and finite detector row. The algebraic (P_M) and its eigenrelation are supplied. Instantiating the records needs the modular curve reduction and supersingular correspondence layer; a single stage needs only the class-to-point specialization with those identities and the finite torsion comparison. |
| Same actual stage and parameters, support coverage and budget | 8209–8212, 8415–8418, 8452–8479, 9450–9455, 9471–9489, 9578–9584, 10236–10252 | `rc-stage-map` and ELLIOT stage data: identify the supplied order level, detecting prime, extracted index `m = |h_*|` and detector with the selected skeleton stage, and the full intrinsic filter with the source. Put primes over `6ℓ` in the Fourier support and its excluded primes in the type conductor. Choose `W, R` with `B ≤ W + 1` and `R ≥ 2`. Given these comparisons the good-prime transfer and equality of elliptic coefficients are proved. |
| (O.4) local theta weights, character values and frame comparisons | 8424–8426, 8495–8576, 8600–8621, 9045–9093 | ELLIOT App F input `PMLocal`: integral weights on finite norm spheres, conjugation and norm character, zero at the zero sphere, root character and its inverse, multiplicative `η` with the stated good values, line indexing and the three local frame comparisons. The permitted two-power order for `s` is part of this character data. These are on one order and one ring. The integral and reduced weights are no longer independent. |
| Exact Fourier sieve and squarefree stage support | 2530–2532, 8496–8566, 9094–9098, 9471–9483 | ELLIOT: for each prime in the actual coefficient support the integral Fourier coefficient vanishes at indices divisible by that prime; the squarefree coefficient is zero in the stage ring off the full intrinsic filter. These are the exact two support statements in the final application. |
| (O.7) and chosen representatives | 2074–2086, 2522–2538, 9101–9405, 9675–9680, 9694–9704 | ELLIOT: `O7Comparison` for the same weighted source, representative and intrinsic filter. The existing `ComparisonCore` plus the permitted phase supplies it for the integer multiplier times the lifted Kummer value. The actual embeddings and the point comparison are out of scope. |
| Advancing precision, (F.5), and the minimum on the full intrinsic filter | 9385–9402, 9407–9445, 10151–10250 | Existing stage and visibility work; the fixed visible witness and (F.5) suffice for `integerDepth_of_witness`, and `integerDepth_of_data` uses the attained minimum on that filter. A minimum proved only on a narrower address filter does not supply this premise. The chosen `IntegerDepth` is the stagewise argument of `inputs_of_pm`. |
| Compatible realization and Fourier comparison | 9638–9668, 9670–9679, 9762–9797, 9919–9921 | `rc-o12-realize`: one compatible `GaloisConstituentModel` with `FourierData` for every tested set and its subsets. The comparison `hexp` identifies all coefficients, including the constant term, with the stated `FourierF` on that lattice. The fixed coefficient place, maximality, and integral inclusion are part of this model; use the same coefficient ring for the weights. The manuscript's spaces are chosen for a set and its subsets, so a finite pool alone cannot instantiate the current global API. |
| Simultaneous good operator data, formwise Hecke and inertia | 9660–9668, 9688–9694, 9712–9733, 9745–9750, 9754–9769 | `rc-o12-formwise` and realization: `ops`, `DF`, `hDF`, and `A.FormwiseHecke` on this same model. Where the ambient data already give the good formula, reuse them; at excluded good primes the first reading still needs the formula on `F_U`. For model construction, formwise inertia must fix the active constituents away from stationary support and the form's primes. |
| Stationary type, quotient and representatives | 2017–2029, 9663–9668, 9745–9750, 9919–9926, 9932–9944 | ELLIOT and existing model glue: `IsTypeChar`, the finite quotient and combined radical detection, and the existing Chebotarev representative property. The ambient operator exclusions need not lie in the stationary support. |
| Two fresh readings | 9705–9717, 9734–9745 | `rc-two-fresh`: the two-fresh field of the model for these same forms. |
| Same-lattice local input | 9754–9892 | Local block owners and `rc-o12-eis-constituents`: `LocalInput A`, i.e. for each tested added prime and local pair, the cuspidal and Eisenstein block identities together with the coefficient-one comparison for (U_p^{(2)}). Existing prints only. |

Once these data are supplied on the selected stage, the application returns both fields of the unchanged `GaloisConstituentModel.Inputs`. No exact recurrence for arbitrary integral coefficient lifts, equality of the two good domains beyond the transfer, or assertions at unbounded stage weights are needed.

## Manuscript check

- Tex 2026–2029, 9471–9483 — OK: later label exclusions restrict the tested primes without adding any Fourier sieve.
- Tex 2068–2086, 9675–9680 — gap filled: the padic coefficient symbol on the prime product equals the integer test; the distinct-factor count is the vertex count.
- Tex 2081–2086, 9699–9704 — OK: when the threshold lies below the retained precision, the two integer divisibility tests determining the symbol are invariant under a change of representative.
- Tex 2522–2538, 8496–8566 — unverified: exact zero outside the full squarefree filter is the local Schwartz support input.
- Tex 8424–8426, 8504–8512 — OK: multiplying a two-power phase by a quadratic sign still gives a two-power phase at good primes.
- Tex 8439–8490 — unverified: the finite detector and geometric specialization identities are the hypotheses of the existing geometric construction.
- Tex 8476–8494 — OK: applying the additive evaluation to the specialization gives the finite eigenfunction; its chosen integral lift and its stage image have the same residue.
- Tex 8600–8621 — OK: the actual integral weight is computed with the integer mass factor, and its reduction gives the same sum used by App F.
- Tex 9045–9076 — unverified: the local sphere and neighbour comparisons are assumed on the actual local weights.
- Tex 9059–9093 — OK: the existing weighted adjointness and local comparisons transfer the Hecke eigenrelation and give (O.6) with `(-1/p)` in the stage quotient.
- Tex 9092, 9472–9478 — unverified: the local zero at index zero and the integral sieve are inputs; the former is passed through the integral sum and the latter through stage reduction.
- Tex 9101–9405 — unverified: (O.7) is upstream; its existing comparison theorem gives the stage equality from the orientation and reduction data when instantiated.
- Tex 9450–9455, 9471–9489, 9578–9584 — OK: one stage, one integer depth and one budget are used for both divisions, uniformly over the allowed operator sets.
- Tex 9585, 9593–9594 — OK: the single elliptic Dirichlet coefficient has the mod-four congruence at all good primes of the actual source.
- Tex 9638–9668, 9670–9679 — unverified: the formwise Galois attachments and compatible Fourier realization are separate requirements.
- Tex 9681–9698 — OK: the inherited fresh reading uses the same divided source coefficient and its reduced residue at coefficient one.
- Tex 9705–9717, 9734–9750 — unverified: the model still needs the two-fresh and formwise comparisons on the actual forms.
- Tex 9754–9892 — unverified: the local block and Fourier comparison are unchanged.
- Tex 9893–9926 — OK: the inherited omission proof uses the first-shell relation at retained precision and the representatives in the same model.
- Tex 10175–10207 — unverified: the coarse bound and the fixed visible witness (or attained minimum) are upstream; the existing finite-cutoff argument is reused.
- Tex 10208–10234 — gap filled: App G's eventual bounds are passed first to the integer representative, then to the same weighted series in the stage quotient.
- Tex 10236–10252 — OK: for output sizes through `W + 1`, the tested-depth bound is untruncated and the precision exceeds the test exponent. The same stage is not asserted to work at unbounded weights.

## Verification

All three new files compiled individually with `lake env lean -j1`, with a single Lean job and the host load and memory checked before each invocation. The 23 `#print axioms` checks reported only `propext`, `Classical.choice`, and `Quot.sound`. No new printed-form leaves were added.
