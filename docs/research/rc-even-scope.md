**Scoped stop.** The even expansion and the fresh-prime reading have a per-set budget interface at one fixed coefficient place. It supplies fixed-set factorization, primary isolation and the unit seed. The actual characteristic-zero inventory is still open. The existing (O.12) consumer additionally needs a joint comparison of the trace orbits at `U` and `U.erase p`; tex 9919–9921 explicitly calls for a joint quotient for this pair. No shared constituent space for the budget has been constructed. Inherited manuscript error: the integer-multiplier shorthand at tex 8162–8167 omits the base coefficient. The exact recurrence and product at tex 8168–8182 are used instead.

The fixed data are a number subfield `F ⊆ ℂ`, its chosen height-one prime `v` above two, and one source `C₀` in the valuation ring of the completion at `v`. The interface takes the components of the place directly: use `F := PhaseField e`, `v := V.v` and `V.aboveTwo` from `EvenPlace.Place`, with `EvenPlace.sourceAtPlace` and `sourceAtPlace_eta_phase` for the fixed source. Its two completion types are definitionally those of the place producer. The place producer is on a separate branch; the Lean files here depend only on the given base.

Inside the quantifier for a good `U` with `U.card + 1 ≤ B`, choose `X_U`, `FourierData X_U`, a finite complete valued extension of the fixed completion, and a compatible complex embedding. The source coefficients, phase values, depth shift and parity stay fixed. The extension ring map commutes with the field inclusion; the extension absolute value restricts to the fixed absolute value. Divisibility by an integer power of two uses the fixed threshold `‖(2 : FixedField v)‖₊ ^ a`, and reduction of a base integer tests the same fixed absolute value against 1 in each extension. Thus the scale is independent of any extension uniformizer. The numerator pays the whole power in the fixed ring, and the comparison is an equality with the image of the expansion already divided there. No identification of residual field elements outside the base image is assumed.

## New Lean results

The declarations are in `ZInQ.Manuscript.RC.EvenJoin`.

| Declaration | What it supplies |
| --- | --- |
| `FixedPlaceExtension.apply_ringMap`, `two_pow_dvd_iff`, `reduce_eq_zero_iff` | Compare the integral and field maps, express integer-power divisibility by the fixed threshold, and read reduction on the image of the fixed ring. |
| `FixedPlaceExtension.source`, `fixedH`, `fixed_numerator_dvd` | Transport only the receiving ring and field. Construct the divided series and exhibit its integer-power divisibility in the fixed ring. |
| `coordinate_match_of_seed_scoped` | For this set, compare descended inventory coordinates with the model using a column identity and the constructor's seed identity. |
| `map_fixed_theta`, `evenExpansion_joined_scoped` | Identify the receiving ring's theta product with the transported integral theta product; identify all positive coefficients of the joined form with it without any transformation-law premise. |
| `budgetRealization_of_joined_scoped` | Assemble `BudgetRealizationScoped` from one comparison, formwise good-Hecke input and local blocks per set. |
| `coefficient_one_scoped` | Read the fresh-prime coefficient of the one seed from the fixed source's valuation symbol. |
| `trace_join_at`, `fixedU_of_joined_scoped`, `primary_of_joined_scoped` | Factor the one trace orbit through the retained quadratic labels; give the original fixed-set factorization and primary reading. |
| `unitSeed_of_joined_scoped`, `rules_and_seed_of_joined_scoped` | Give the original unit seed; recover the original coefficient rules when the existing (O.12) deletion reading is supplied. |
| `finite_constituent_compositum`, `evenSeed_coeff_fixedRing` | Gather the number fields of a supplied finite list of constituents, and show that the inventory vector's coefficients lie in the image of the fixed ring before constructing a lattice or a model column map. |

`FixedPlaceExtension` gives a field and ring comparison, finite dimension, completeness and the normalization of the valuation. That is strictly less data than a model realization: it does not mention an inventory, a seed, complex Fourier coefficients, or a trace reading (tex 9638–9654). `HeckeAt` asserts only the characteristic-zero good-Hecke coefficient formula on one seed (tex 9660–9662, 9688); `LocalAt` restricts the existing local attachment to that set (tex 9754–9902). They do not assert the identification of that seed or the valuation reading. `BudgetRealizationScoped` is the resulting package consumed by the reading proofs; it includes an integral expansion identity and algebraic operator data, but no assertion equating two readings, no graph rule and no unit seed. The abstract carrier `Model P hS B` is unchanged. Its trace-operator data still use that existing type; the scoped interface gives no interpretation of its off-set seeds as actual forms and never invokes its old all-set `Inputs`.

## Consumer audit and integration

VERIFIED by `git grep`: the old producer is `EvenBudget.budgetRealization_of_blocks` (called by the old join). In `AuxInputs/Assembly.lean`, the first substantive consumer of `EvenSource.BudgetRealization` is `EvenSource.rules_and_seed`; `symbolFamily_rules` and `symbolFamily_seed` take its two projections. `auxFactorInputs_of_realizations`, `auxFactorInputs_of_compatible_partition`, `auxFactor_of_realizations`, and `f3Target_of_realizations` relay those projections. The last takes `EvenUpper33b` as a separate input. No downstream relay inspects the coefficient ring, constituent vectors or valuations.

The integrator should switch the `hReal : ∀ B, P.BudgetRealization hS B` binder at `EvenSource.rules_and_seed` to `∀ B, BudgetRealizationScoped (hS := hS) C₀ i B`, with the same `v,C₀,i` outside `B`. Use `unitSeed_of_joined_scoped` directly for the seed and `rules_and_seed_of_joined_scoped` for the paired handoff when the deletion reading is supplied. Relay these binders through the source family, keeping each source's place and parity before the budget. The existing single-model statements are unchanged.

The rule that still needs a comparison is (O.12). `O12.ThetaData.o12_at_one` uses the one model's reads of `F (U.erase p)` as well as `F U`; `GaloisTraceModel.o12_of_model` uses `N_anti` (restriction of its single quotient to the smaller set) when selecting the four representatives. A choice of models and an equality of base valuations supply neither that restriction nor equality of trace readings on overlapping seeds. The missing scoped argument is to take joint representatives for the two actual trace orbits and common quadratic labels and use the local identity on the `U` model together with the fixed-source omitted coefficient on the `U.erase p` model. It must compare each chosen prime's genuine Frobenius with its specified element in **both** models. With open normal trace stabilizers, an intersection and a test domain avoiding ramification is a possible route (SPECULATIVE here). The old theorem gives no such inter-model comparison. The existing interface for the result of this step is `∀ B, O12Reading (evenTypes W.S hS.1) P.reading (fun p => (Ecurve ℓ).LFunction p) B`; it is the unchanged deletion reading, not a new leaf or a proof of it. Owner: the lead and the local trace integration.

## Fixed-set inventory stop

For one tested set use the moving block and the finite family indexed by `subscripts U` at their intrinsic levels `movingLevel P U` and `maskedLevel P * j.val`. The first unsupplied analytic statement is a finite list of normalized characteristic-zero cuspidal and weight-two Eisenstein columns with their old degrees and characters, such that the **positive Fourier expansions of these blocks** lie in the complex spans of the matching columns. For a block of intrinsic level `m` and character `χ` pulled back to a common level, the index restriction is exactly `Y.level a ∣ m ∧ Y.χ (Y.origin a) = χ`. There is no need for a span at any unrelated level or character. The current reusable descent theorem can take the stronger existing `SpansOverComplex Y κ`; its restriction to these blocks is the missing mathematical input. The individual coefficients and diamond values of the columns must be placed in their number fields, independently of the expansion of the joined seed. Retain independent positive columns with these level and character restrictions.

In the inventory vocabulary, the precise span obligation for each of those blocks is

```lean
(fun n => κ (a n)) ∈ Submodule.span ℂ
  {c | ∃ x, Y.level x ∣ m ∧ Y.χ (Y.origin x) = χ ∧
    (fun n => κ (Y.expansion x n)) = c}
```

Here `a` is the formal expansion with its zero slot set to zero: it is either `timesTheta (TL phase U.toList source)` or `timesTheta (unaryCoeff good phase i j.val)`, as in `evenCoordinates`. This asks for the spanning of the blocks separately, before their scaled linear combination or any comparison with a model.

VERIFIED: `HeckeRing.GL2.Newform.span_levelRaise_eq_top` is available for the cusp space, and the tree has individual newform coefficient field results. The existing Eisenstein divisor-sum and local calculations do not give the primitive analytic form or its occurrence in a basis. Even before spanning, the missing Eisenstein existence assertion for the occurring ordered pairs is a genuine `M₂(Γ₁(m₁m₂), χ₁χ₂)` form with positive coefficients `∑_{ud=n} χ₁(u) χ₂(d) d`, at the product of the conductor moduli, with the degeneracy factor kept separate. The trivial pair in weight two requires its level-raised holomorphic combinations where applicable, rather than treating the level-one weight-two series as a holomorphic form. Neither holomorphy of the source nor cuspidal spanning supplies that analytic input. The generic Mathlib Eisenstein construction in weight at least three does not provide the weight-two result. Size: substantial modular-form theory and a local model construction; no additional printed leaf is registered.

After choosing one compositum for this finite list, a place above the fixed `v` and compatible embeddings still have to be instantiated. In a model constructed with the inventory's `Basis.coefK` and the computed `evenSeed` as its seed at `U`, the required identifications are the constructor identities
```lean
(∀ w n, X.coefK (ι w) (A.index n) = (Y.toBasis hc).eval n.val w) ∧
(X.F U).val = ι (evenSeed hS i U hU hodd (E.source C₀) Y hm hc κ hκ hspan)
```
where `ι` is a field-linear map from the inventory coordinates to the model coordinates. They do not follow for an arbitrary preselected abstract `X`. `evenSeed_coeff_fixedRing` supplies integrality of the column evaluation on the seed, and `coordinate_match_of_seed_scoped` then supplies the comparison after the two identities. What remains is to build the actual inventory, attach its representations and integral lattice, and produce `HeckeAt` and `LocalAt` at that set (tex 9649–9668, 9754–9902; owner: the lead and the constituent and local model work). No cross-budget field of constituents is needed.

## Count and known issues

- Registered LEAF and GLUE counts are unchanged. The new Lean results discharge the one-set transport, normalization, and the fresh-prime, fixed-set, primary and seed uses of the scoped handoff. The inventory and the joint deletion comparison remain GLUE. No pinned statement changed.
- The old single finite-level realization route is conditional on an unsatisfiable single-level premise for `B ≥ 2`, by `no_common_level`. This is a constraint on that realization route, not a nonexistence proof for arbitrary abstract carrier models.
- Inherited issue at tex 9663–9668: integrality of a good Hecke image does not place it in a diamond-only span. Use the existing lattice generated by good Hecke and diamond translates.
- No new manuscript error was found. The normalization error at tex 8162–8167 is inherited. No page or theorem number is asserted from memory.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 8162–8167 | error | Inherited missing base coefficient in the multiplier shorthand. |
| 8168–8182 | OK | Exact multiplier normalization. |
| 9471–9496 | OK | Fixed source support and set of moving operators. |
| 9497–9546 | gap filled | Existing actual moving transformation. |
| 9548–9555, 9618–9625 | gap filled | Existing unary transformation on positive squarefree shells. |
| 9626–9636 | OK | Exact integer division and parity at the fixed source. |
| 9638–9646 | gap filled | Divisibility in the fixed ring and faithful reduction after extension. |
| 9647–9648 | gap filled | Actual weight-two Fourier series and its transfer from the per-set seed. |
| 9649–9654 | unverified | Scope and finite compositum isolated; actual weight-two constituent list and completed extensions are open. |
| 9655–9668 | unverified | Integral translate generation and attached Hecke and trace operators are per-set model inputs. |
| 9670–9704 | gap filled | Coefficient at a fresh prime reads the same fixed valuation symbol in the scoped handoff. |
| 9712–9740 | OK | Existing determinant and trace identities are used within the one carrier. |
| 9741–9750 | gap filled | The orbit on one set factors through its elementary quadratic labels using existing determinant and double-trace data. |
| 9754–9764 | unverified | The characteristic-zero span must retain intrinsic levels, characters and old degrees. |
| 9765–9902 | unverified | Local attachments and the resulting operator comparison need realization. |
| 9905–9918 | OK | Existing fixed-source omission calculation precedes the joint comparison. |
| 9919–9945 | unverified | The joint quotient for the two scoped trace orbits is still needed. |
| 9947–9948 | gap filled | The scoped primary reading vanishes via `t(1) = 2`. |

## Verification

VERIFIED: [Scoped.lean](../../ZInQKernel/Contrib/OneProof/RC/EvenJoin/Scoped.lean), [ScopedConsumer.lean](../../ZInQKernel/Contrib/OneProof/RC/EvenJoin/ScopedConsumer.lean), and [ScopedInventory.lean](../../ZInQKernel/Contrib/OneProof/RC/EvenJoin/ScopedInventory.lean) passed direct `lake env lean -j1` and individual Lake target builds. The [scratch audit](../../scratch/rc-even-scope/Audit.lean) passed for 23 declarations, including every new theorem. The [axioms output](../../scratch/rc-even-scope/axioms.txt) contains only `propext`, `Classical.choice`, and `Quot.sound`.
