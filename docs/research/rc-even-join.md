**Scoped stop.** Both half-integral laws are joined. The fixed even expansion and its budget consumer have no moving or unary transformation premise. For a supplied characteristic-zero inventory, the actual moving and unary blocks descend to coordinates over the coefficient field, with their individual level and character support. The remaining step is to construct and match those inventories to one budget model at one compatible place. The manuscript chooses its finite constituent space for a fixed set (tex 9649–9654); that choice does not construct the simultaneous model.

## Lean results

The declarations are in `ZInQ.Manuscript.RC.EvenJoin`.

| Declaration | What it supplies |
| --- | --- |
| `unary_on_subscripts`, `exists_joinedForm`, `joinedForm`, `joinedForm_coeff` | Every tested squarefree shell index is positive. The proved moving and unary laws give the actual weight-two form and its expansion at every index. |
| `evenExpansion_joined` | At a fixed compatible embedding, transfer the actual expansion to the integral lattice from the positive coefficient match. Both transformations are discharged. |
| `budgetRealization_of_joined` | Supply the exact even coefficient row of `budgetRealization_of_blocks` from the match, with one `X,A,C,i,κ` across the budget. The previous Hecke, residue and local-sector premises are retained. |
| `map_moving`, `map_unary`, `map_theta`, `moving_zero`, `unary_zero` | Commute with the coefficient embedding and check the zero slots for the separate blocks. |
| `unitCharacter_lift`, `movingCharacter_lift`, `unaryCharacter_lift` | Descend the actual diamond characters via the phase values and integer quadratic symbols. |
| `blockCoordinates`, `evenCoordinates` | Use `spansAt_of_complex` then `coordinates_of_span` on each actual character block; `evenVector_eval` evaluates their exact linear combination as the actual form under `κ`. The normalization uses the unscaled field lift of the source and its original depth; the existing place comparison cancels the matching shift in the integral source. |
| `exists_evenSeed`, `evenSeed`, `evenSeed_eval`, `coordinate_match_of_seed` | Select the coordinates of the joined form in the supplied inventory. Compatibility on the columns and construction of the seed give the exact comparison in the budget model, using `expand_spec` and `FourierData.expand_coeff`. |
| `no_common_level` | If `B ≥ 2`, no positive integer is divisible by every tested moving level. A singleton at a sufficiently large good prime already fails. |

## Exact remaining obligation

For a given `P,hS,B`, choose one `X : Model P hS B`, `A : FourierData X`, `C : SourceAtPlace P X.O X.K`, parity `i` and `κ : X.K →+* ℂ` with `κ.comp C.eK = C.eC`. The parity is supplied by the existing `exists_unary_parity`. For these choices, the smallest missing premise of the expansion and budget handoff is exactly:

```lean
∀ (U : Finset ℕ) (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p),
  U.card + 1 ≤ B → ∀ n, n ≠ 0 →
    κ (algebraMap X.O X.K (A.coeff n (X.F U))) =
      (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n
```

The constituent route to this statement (tex 9649–9654, 9754–9764; owner: the lead) is as follows. For each tested `U`, supply an `Inventory I J X.K T N` with `movingLevel P U ∣ N`, a test domain coprime to `N`, and `SpansOverComplex Y κ`. The index and level can depend on `U`. With `hc` the coprimality proof and `vU := evenSeed … Y … κ …`, supply a linear map `ι : (I → X.K) →ₗ[X.K] (X.I → X.K)` such that

```lean
(∀ v (n : O12.PosIndex), X.coefK (ι v) (A.index n) = (Y.toBasis hc).eval n.val v) ∧
  (X.F U).val = ι vU
```

Thus it suffices to identify the inventory columns in the model and use the constructed seed as its `F U`. Constructing this data is substantial: the finite characterwise spans need normalized cuspidal and Eisenstein constituents with degeneracies in the chosen field, and the field, residue comparison, lattice and embeddings must work jointly for varying levels. The tree has cuspidal old/new spanning (`HeckeRing.GL2.Newform.span_levelRaise_eq_top`) and individual newform coefficient fields, but the checked complex descent in `BlocksPerU` assumes its inventory spans. A per-pool construction or a choice of a new place for each `U` does not give the displayed statement. A compatible assembly of formwise spaces is a possible route (SPECULATIVE); the existing model does not assume a finite constituent index type.

No new hypothesis structure or Prop was introduced. `SpansOverComplex` is the existing characteristic-zero span assertion for a supplied inventory, prior to any model, lattice, choice of seed or trace law (tex 9649–9654, 9754–9764). The column comparison concerns all vectors in that inventory and does not fix the seed; the seed identity concerns the underlying vector and does not assert any Fourier formula or trace identity. Their use keeps the construction separate from the coefficient match, and neither contains the budget conclusion.

The consumer still needs `X.m.IsMaximal` at the chosen place (tex 9638–9643), the existing phase premise `∀ p, T.Good p → ∃ t : ℕ, C.η p ^ (2 ^ t) = 1` (tex 7943–7944; App E producer), `A.FormwiseHecke` (tex 9660–9668; formwise operator glue), and the existing `Nonempty (O12Local.Stage A U Q hp.ne_zero)` for every tested local pair (tex 9754–9864; local constituent glue). The place and the instantiated constituent data are the lead's remaining assembly. With these data the new consumer gives exactly `P.BudgetRealization hS B`; the existing `O12.inputs_of_theta` and the auxiliary factor consumers then apply at their original quantifiers.

## Count and known issues

- GLUE: two transformation premises removed from the joined handoff, and the per-set descent and constructor comparison are proved. The budget coordinate realization stays open. Zero change to registered claims, LEAF counts or pinned statements.
- Inherited manuscript error (tex 8162–8167): the integer-multiplier shorthand omits the base coefficient. The usable normalization is the explicit product at tex 8168–8176. The join does not rely on the shorthand.
- The finite-level obstruction is to the direct reuse of a single finite inventory in the budget interface. It does not contradict the manuscript's fixed-`U` choice nor rule out a larger simultaneous model.
- Literature attachments for the local representations are outside this pass. No external theorem or page locator is asserted from memory.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 8162–8167 | error | Inherited normalization error described above. |
| 9471–9496 | OK | The set uses the fixed source support and its actual raw moving operations. |
| 9497–9546 | gap filled | The proved fresh-prime law iterates on the actual even source. |
| 9548–9555, 9618–9625 | gap filled | The proved weighted unary law applies at each positive squarefree shell with matching parity. |
| 9626–9636 | OK | Integer division and the matching-parity formula are the exact existing divided series. |
| 9638–9646 | OK | The lattice comparison uses the chosen place and the existing exact integral lift. |
| 9647–9648 | OK | The actual weight-two form has the ordinary theta convolution at every index. |
| 9649–9654 | unverified | The finite characterwise inventory and the common place for varying tested sets still need construction. |
| 9655–9668 | unverified | The stable lattice and formwise Hecke data are existing inputs to the consumer. |
| 9754–9760 | gap filled | Conditional on the characteristic-zero inventory, descent retains the intrinsic levels and separate characters. |
| 9762–9771 | unverified | The coordinate bridge works once the characteristic-zero and model columns have been identified; it does not construct the attached representations. |
| 9773–9864 | unverified | The instantiated local cusp and Eisenstein data are separate consumer inputs. |

## Verification

VERIFIED: the three imported targets built with serial Lake commands. [Joined.lean](../../ZInQKernel/Contrib/OneProof/RC/EvenJoin/Joined.lean) and [Coordinates.lean](../../ZInQKernel/Contrib/OneProof/RC/EvenJoin/Coordinates.lean) both passed direct `lake env lean -j1` and their module builds. [The scratch audit](../../scratch/rc-even-join/Audit.lean) passed for 19 theorems and two definitions, including private helpers. [The printed axiom sets](../../scratch/rc-even-join/axioms.txt) use only `propext`, `Classical.choice`, and `Quot.sound`.
