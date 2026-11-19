**Result and scoped stop.** The fixed-set realization and consumer port supplies the existing `O12Reading T R₀ ap B`, `FixedUFactorization T R₀ B`, and `PrimaryReading T R₀ B` from the actual odd-stage windows and the named inputs below. These are the types of the original constituent consumers. They feed the unchanged `symb_contraction` and, with `ApEven`, `rulesUpTo_symb`. The port needs no global constituent space and no comparison between the trace operators of different windows. The first unresolved analytic existence claim is the weight-two block realization for **one** fixed set and its subsets, with its attachments. It is stated below. The full rules remain conditional on that realization and the upstream inputs.

Route **B** follows tex 9649–9654 and 9919–9921: take the pool to be the fixed operator set `U`, and realize `U` and all its subsets in that space. The given construction only identifies coefficients on subsets of its pool. If `B ≥ 2`, `window_misses_test` exhibits a tested singleton outside any one pool, so the given realization cannot supply route A's global expansion hypothesis. This does not rule out a different global theory. In B, a single use of (O.12) transports both forms through the same quotient and reads both against the same symbol `R₀`. The global dictionary conclusions arise by quantifying that proof over the tested roots. This reindexing and zero-extension bookkeeping are on-the-spot (c).

## Statements

Here `FreshAt X V q` is `R₀ (insert q V) = traceRead X V (X.frob q)`, where `traceRead` is the coefficient-one reading of the coefficientwise reduced trace orbit. `OmissionAt X U p` is the second conjunct of `X.Inputs` at that pair, with its same signs, type, bits, and reduced readings. `ReadingsOn X U avoid` requires `FreshAt` on subsets of `U` for good fresh primes outside `avoid`, and `OmissionAt` for each `p ∈ U`. Tested roots are good and satisfy `U.card + 1 ≤ B`.

| New theorem | Statement and consumer |
| --- | --- |
| `o12_at` | On one tested `U`, `ReadingsOn X U avoid` and `IsTypeChar T χ` give, for every `p ∈ U`, prescribed type and bits, exactly the four-prime product-label witness in `O12Reading` at that input. The proof chooses all four primes outside `U ∪ avoid`. Supplies the pointwise conclusion of `o12_of_constituents`. |
| `traceRead_eq_of_labels` | At a tested `U`, equality of `χ(g)` and `χ(g')` and of all `bitChar s` for `s ∈ U` implies `traceRead X U g = traceRead X U g'`. Supplies the orbit comparison used by `fixedU_at` and `primary_at`. |
| `fixedU_at` | For two prescribed good fresh primes with the same type and bits at a tested `U`, their two `FreshAt` hypotheses in the same space imply `R₀ (insert q U) = R₀ (insert q' U)`. This is the pointwise conclusion of `fixedU_of_constituents`. |
| `primary_at` | A prescribed good fresh prime of trivial type and bits at a tested `U`, with `FreshAt`, has `R₀ (insert q U) = 0`. This is the pointwise conclusion of `primary_of_constituents`. |
| `o12_of_windows` | `IsTypeChar T χ` and `∀ U` tested, `∃ X avoid, ReadingsOn X U avoid`, imply `O12Reading T R₀ ap B`. Supplies `hO12` of `symb_contraction` and `rulesUpTo_symb`. |
| `fixedU_primary_of_windows` | `IsTypeChar T χ` and `∀ U` tested, `∃ X, ∀ q` good and fresh at `U`, `FreshAt X U q`, imply `FixedUFactorization T R₀ B ∧ PrimaryReading T R₀ B`. Supplies `hswap` of `symb_contraction` and `hswap`, `hprim` of `rulesUpTo_symb`. |
| `rulesUpTo_of_windows` | The two window families at `B = W + 1`, `IsTypeChar T χ` and `ApEven T ap` imply `RulesUpTo ε (symb T R₀) W` by the existing dictionary. |
| `fresh_at_on_stage` (private) | Actual expansion at a subset `V ⊆ U`, the stage valuation input, and the equality of trace coefficient one with coefficient `q` of `F_V` give `FreshAt X V q` within the root's budget. Supplies fresh readings to both stage bridges. |
| `trace_one_of_good_data` (private) | Ambient good-operator and determinant Fourier data imply that coefficient-one equality at a good prime outside their exclusions. Supplies the comparison to `fresh_at_on_stage`. |
| `readings_on_of_stage` | Actual expansions on one root and its subsets, good operators and their Fourier data, the stage valuation, the phase order and `LocalOn` give `ReadingsOn X U avoid`. Supplies the window input of `o12_at`; it uses the two existing pointwise stage theorems. |
| `root_readings_of_stage` | The stage expansion and valuation at a root, the ambient Fourier operators there, and `ExcludedAtOne` give `FreshAt X U q` for every good fresh `q`. Supplies the prescribed-prime hypotheses without requiring `LocalOn`. |
| `expansions_on_window` | In the model returned by `commonSpace`, every subset `V` of the pool satisfies `A.coeff n (X.F V) = E.FourierF D hV n` at every index of the existing coefficient family, with `hV := P.admissible V hVU`. Supplies `ExpansionsOn` to the stage bridges. |
| `readings_on_window` | For a tested pool, `commonSpace` with the stage valuation, phase and same-lattice local input supplies `ReadingsOn X P.pool avoid`. This is the per-pool application of `readings_on_of_stage`. |
| `root_readings_on_window` | For a tested pool, `commonSpace` with its stage valuation and `ExcludedAtOne` supplies all `FreshAt X P.pool q` at good fresh primes. This is the per-pool application of `root_readings_of_stage`. |

`poolOfTest` takes the root itself as the pool. `commonSpace` uses the existing `windowModel`: the two-fresh hypothesis extends by zero outside the pool; any nonzero seed belongs to the pool, so its formwise inertia comparison is enough even when the constructor is tested on a larger set. No fresh reading is proved on those zero extensions. `realizedSpace` names the resulting model and its Fourier data.

## Remaining hypotheses

At a fixed actual stage and tested `U`, take `P := poolOfTest U …`. After choosing the finite coefficient extension, a lift of the **same** stage there, a finite constituent index type and common-level Hecke domain, the missing realization Prop, in the existing types, is:

```lean
∃ (A : ThetaCoeff.Basis I K G (ThetaCoeff.Test T avoid))
    (C : ThetaCoeff.DiamondCharacters O G E.η),
  Nonempty (ThetaCoeff.Blocks (P := P) A E D C) ∧
  Nonempty (ThetaCoeff.Attachment A frob)
```

Here `E : Lift S` and `D : Divisions E δ W R adm` are fixed over those coefficient choices. The existential is needed for each tested `U`, with choices allowed to vary by `U`; the choices must extend the same actual source, characters, depth and stage. The analytic task is to produce these finite data for that source. It involves the weight-two modular realization of the theta blocks, the oldforms and diamond actions, and the characteristic-zero attachments; this is substantial theory, not a bound on a prime pool. Nothing is inferred by selecting unrelated stage symbols. Once supplied with the following inputs, one such witness proves the local readings and a family yields the three dictionary hypotheses at the fixed budget.

| Exact hypothesis or input | Tex and owner |
| --- | --- |
| The finite `Blocks` and `Attachment` existential above, on a finite coefficient extension. `commonSpace` uses the chosen field/ring, topology, injective embedded integral inclusion, maximal ideal above two with finite residue field, and genuine good Frobenius choices. | 9548–9555, 9620–9625, 9638–9668, 9762–9797. ELLIOT input (substantial weight-two realization and attachment theory). The already-used good polynomial and Chebotarev statements enter through existing interfaces. |
| Actual `S : ThetaStage (StageRing O M)`, its `Lift S`, and `Divisions E δ W R adm`, with the same geometric weights, stages and reductions under coefficient extension; `∀ p ∈ U, S.Good p` for each tested root and `B ≤ W + 1`. The elliptic coefficient in the constructed model is `S.ap` definitionally. | 8422–8426, 8476–8494, 8600–8621, 9059–9082, 9447–9489, 9699–9710. Sibling `rc-pm` for the weights and lift; existing stage/division and good-domain comparison data. No exact recurrence on the integral lift is needed. |
| `StageValuation`: on the tested sets in budget, `read` compares `R₀` with the intrinsic valuation threshold; `onFilter` gives the lower bound and the phase times the integer representative at stage precision; `offFilter` gives stage zero. | 2074–2086, 2522–2538, 9675–9704. Sibling `rc-o12-stage-val`. |
| `∀ p ∈ U, ∃ k : ℕ, E.η p ^ (2 ^ k) = 1` on the lift, for omission. This is the phase order at the added primes, distinct from equality of phases after stage reduction. | 8422–8426, 9696–9698, 9908–9918. ELLIOT phase/lift comparison. |
| `TwoFreshOn V ρ₀ hinj hfrob B`: for `V' ⊆ P.pool` in budget, every positive coefficient of `t(g)t(h)F_V'` belongs to `m`, for all `g,h`. | 9712–9717, 9741–9745. Sibling `rc-two-fresh`. |
| `InertiaOn V ρ₀ support`: for a tested seed `V' ⊆ P.pool`, at good `q ∉ support ∪ V'`, inertia fixes each constituent coordinate where the seed is nonzero. | 9745–9750, 9754–9771, 9922–9924. Sibling `rc-o12-formwise` (`hseed`). |
| `LocalOn A U hU`: for `p ∈ U` and each `P : LocalPair p`, there exist `Dp : LocalBlocks X U P` and `A.UpAtOne Dp (hU p hpU).1.ne_zero`. | 9754–9892. Siblings `rc-o12-local`, `rc-o12-eisenstein`, `rc-o12-eis-constituents`. Only needed by the omission consumer. |
| `ExcludedAtOne A U avoid`: `∀ q, T.Good q → q ∉ U → q ∈ avoid → A.coeff 1 (X.tΛ (X.frob q) (X.F U)) = A.coeff q (X.F U)`. Automatically vacuous if every good ambient exclusion belongs to the root. | 9660–9668, 9670–9674, 9688–9694. Sibling `rc-o12-formwise` (`hexcl` restricted to the root and coefficient one). Only needed for prescribed-prime readings; the four representatives in (O.12) can avoid all ambient exclusions. |
| `OpenTypeKernel χ`, `IsTypeChar T χ`, `TypeDetectsRadicals χ support`, `T.m.primeFactors ⊆ support`, and `2 ∈ support`. For the dictionary rules, also `ApEven T ap`. | 2017–2025, 9585–9593, 9745–9750, 9932–9944. Existing stationary type and elliptic-curve comparison data. The ambient Hecke exclusions need no stationary support coverage. |

## Known issues

- Inherited source error: `ThetaCoeff/Model.lean` still applies the removed `hdiam` argument to `buildConstituentModel`. The new imports bypass that wrapper and use `O12Theta.windowModel`.
- The old single-support constructor would require ambient exclusions to lie in stationary support, incompatible with a nonempty pool in the recorded stationary type setup. The split support of `commonSpace` uses the existing repair.
- Tex 9660–9668: the inherited lattice proof closes the generators under both good Hecke and diamond operators; integrality of a good Hecke image alone would not prove membership in a diamond-only span.
- The stage proof stays at finite precision. It does not discharge the stronger exact-lift signed recurrence in `O12.ThetaData`. The port supplies dictionary Propositions rather than the global `GaloisConstituentModel.Inputs` or a global density model.

## Manuscript check

- Tex 9447–9489, 9675–9680 — OK: choose one operator budget and valid stage before testing; each root and its subsets lie within that budget.
- Tex 9548–9555, 9620–9625, 9647–9654 — unverified: actual block modularity and the finite constituent realization are named inputs.
- Tex 9638–9646 — OK: coefficientwise reduction of the integral lattice suffices, and the existing operator-stable quotient does not assume saturation.
- Tex 9655–9668 — gap filled: the existing lattice includes both Hecke and diamond translates, allowing the scalar operators to preserve it by limits.
- Tex 9670–9704 — OK: fresh coefficient one follows from the actual divided expansion and the retained precision; the root-only comparison covers a prescribed prime omitted by the ambient Hecke tests.
- Tex 9706–9710 — OK: both forms in each omission use the same source and phase data; reindexing the space leaves the coefficient symbol fixed.
- Tex 9712–9717, 9741–9745 — unverified: the two-fresh coefficientwise vanishing is a sibling input.
- Tex 9719–9739 — OK: reuse the determinant Fourier calculation and exact trace identities before reduction.
- Tex 9745–9750 — gap filled: the elementary quotient comparison uses the actual formwise inertia input on subsets and separates stationary support from ambient exclusions.
- Tex 9754–9892 — unverified: the same-lattice active local blocks and bad-prime Fourier comparison remain inputs.
- Tex 9893–9918 — OK: use the reduced local identity and the finite-precision omission congruence on the actual forms.
- Tex 9919–9925 — OK: the common quotient preserves the two trace readings and all retained characters; all four representatives can avoid the ambient exclusions.
- Tex 9926–9945 — OK: the product of type labels and all external bits is transported in `o12_at`; the existing dictionary uses fixed-set invariance, reciprocity and `cp_sum_odd` to give contraction.
- Tex 9947–9953 — OK: the trivial label reads `t(1)`, which vanishes after reduction.
- Tex 9955–9973 — OK: the existing replacement-chain consumer requires fixed-set comparisons, so a change of space between separate comparisons does not change the graph symbol.

## Verification

`Consumers.lean`, `Stage.lean`, and `Window.lean` each compiled with `lake env lean -j1`, serially. All 14 theorem audits (including both private helpers) reported only `propext`, `Classical.choice`, and `Quot.sound`. No new printed-form leaves were added.
