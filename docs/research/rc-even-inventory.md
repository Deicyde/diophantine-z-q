**The finite characteristic-zero inventory is proved for one tested set. The scoped model comparison remains open.** The actual moving and unary weight-two blocks are cuspidal at their own levels. Thus the Eisenstein list for these blocks can be empty, and no general weight-two Eisenstein decomposition is needed. Lean extracts finite lists of genuine normalized newforms with their source levels, characters and old degrees, places the list over a finite extension of the fixed completion, and checks the complex embedding on every positive Fourier column. The lists have not been assembled into the independent `BlocksPerU.Inventory` of one actual scoped carrier. The bridge supplies the per-set coordinate comparison once that carrier is built from those columns and the resulting seed.

Inherited manuscript error: the multiplier shorthand at tex 8162–8167 omits the base coefficient. The exact recurrence and product at tex 8168–8182 are the formulas used. No new manuscript error was identified. In particular, tex 9654 correctly says holomorphy alone does not exclude Eisenstein constituents. The argument here proves vanishing at *every* cusp for the specific forms.

## Actual blocks and their coefficient place

VERIFIED: The moving series starts with the masked App E cusp form. A positive rational affine change of variable transports a cusp normal to a constant times the normal at a rational cusp of the source, at a parameter tending to infinity. This proves that dilation and the finite additive average preserve vanishing. The Fourier calculation identifies the result with the actual moving series. For the unary series, the linear factor kills frequency zero in the resummed Poisson series. The remaining terms are bounded by a summable Gaussian times `exp(-π(y - 1))` for `y ≥ 1`. The Poisson formula sends the imaginary parameter to infinity at each cusp, after separating denominators of either sign and zero. Multiplication by the bounded ordinary theta normal then gives cusp vanishing in weight two. Equality of the width-one Fourier expansions identifies these products with the summands of `evenWeightTwo`, and their combination with `joinedForm`.

VERIFIED: The cuspidal old/new spanning theorem restricts to one character by independence of diamond eigenspaces. For each block of intrinsic level `m`, the resulting list contains genuine `Newform L 2` labels with `d * L ∣ m` and the pulled-back character at `m`. The column at index `n` is the coefficient of the newform at `n/d` if `d ∣ n`, and zero otherwise. The moving block uses `movingLevel P U`; a unary block uses `maskedLevel P * j.val` even when included in the common level. The lists give actual complex linear combinations at every index, including zero.

VERIFIED: The compositum contains the fixed phase field and the number fields of all these lists. One prime over the fixed prime yields the finite extension of completions. Raising the receiving norm to the inverse local degree makes it restrict to the fixed norm without changing completeness, the valuation ring or its maximal ideal. The algebraic complex embedding extends the compositum inclusion by mapping a transcendence basis first. It agrees with the fixed field's inclusion into the complex numbers on elements embedded from the number field. To use the fixed-place producer, specialize `F` to `PhaseField e` and `v` to the chosen `Place.v`. The source comparison `κ.comp (E.fieldMap.comp C₀.eK) = C₀.eC` follows on a source whose two maps are induced by the embeddings of that phase field. The specialization to the producer branch was not compiled here.

## Smallest remaining statement

For this one set, put the actual positive complex columns at `N = movingLevel P U` and identify repetitions with the same normalized newform and old degree. The missing step before `Inventory.toBasis` is a **single independent presentation retaining the intrinsic spans**. Precisely, choose columns indexed by a finite type `I` with `LinearIndependent ℂ col`, with each column's genuine source level, character and old degree and with, for each actual block `b`,

```lean
evenBlockSeries P hS i b ∈ Submodule.span ℂ
  {v | ∃ x : I, sourceLevel x * degree x ∣ evenBlockLevel P b ∧
                 commonCharacter x = liftedBlockCharacter b ∧ col x = v}
```

Here `col x : ℕ → ℂ` has zero slot zero. There is no spanning requirement at unrelated levels and characters. Taking a basis of the unrestricted sum by deleting dependent columns alone does not prove the displayed restricted spans. A direct way to retain all old multiplicities is to prove linear independence of the distinct normalized newform/dilation columns once duplicates are merged. The vendored `Newforms/Decomposition.lean` explicitly stops at spanning and a result for a source whose level divides the ambient level; it does not provide the full direct sum of the old spaces of distinct newforms across levels. Establishing the necessary restricted independence, or a replacement that preserves the displayed spans, is the first remaining constituent step. Owner: the constituent work. Tex 9650–9652, 9754–9764.

After that step, the existing good-Hecke recurrence for a normalized newform is the input for its `EigenSource.cusp`. With the actual labelled columns in `Inventory`, `block_span_of_inventory_labels` supplies the complex span in the precise convention of `coordinates_of_block_span`. The local Galois model still needs `SourceAttachment` on the actual newform at the chosen place: a matrix-continuous representation unramified away from two and its own level, with arithmetic Frobenius trace `a_q` and determinant `qχ(q)` at the good primes, and the known conductor/newline data at the tested primes. The general Carayol attachment is a literature input in the tree, not a construction supplied by this task. The existing cuspidal Whittaker shift and local block lemmas apply to these attached sources after the Fourier columns are identified. The local Eisenstein character split and divisor-sum shift are valid for supplied pairs but are not needed in this cuspidal realization. Owner: the modular Galois and local model work. Tex 9652–9654, 9764–9771, 9773–9864.

The lattice is the integral span of **Hecke and diamond** translates of the needed seeds, with the coefficients and seed taken from the inventory. The odd constructor shows the intended shape. Applying it to the even input requires the even hypotheses for the local model, including its orbit and two-fresh data. This task does not instantiate `HeckeAt` or `LocalAt`. In the model constructor, the positive-index map is the identity and the column and seed equations are
```lean
(∀ w n, X.coefK (ι w) (A.index n) = (Y.toBasis hc).eval n.val w) ∧
(X.F U).val = ι seed
```
where `ι` is the linear map from the inventory coordinates to the model coordinates. `joined_coordinates_of_block_spans` computes the required evaluation of `seed`. `coordinate_match_of_joined_vector` then gives exactly the comparison asked by `budgetRealization_of_joined_scoped` via `A.expand_coeff` and `X.expand_spec`. These equalities are constructor identities, not consequences for an arbitrary preselected carrier. Owner: the scoped model integration. Tex 9655–9668. Keep `BudgetRealizationScoped` as the budget consumer binder; no comparison between distinct sets is used here. The deletion step was left untouched.

## New Lean results

Names below are in `ZInQ.Manuscript.RC.EvenJoin`.

| Declaration | What it discharges |
| --- | --- |
| `affinePoint_zeroAtCusps`, `movingOp_zeroAtCusps`, `exists_cuspidal_moving_series` | Vanishing at every cusp of the moving series, starting with the actual masked form. |
| `weightedTheta_zeroAtCusps` | Vanishing of the unary Poisson series for every positive shell, including cusps outside the transformation group. |
| `theta_product_cuspidal`, `actual_cuspidal_blocks` | The ordinary theta product is cuspidal when its half-integral factor vanishes; this applies to the actual moving and unary blocks of `joinedForm`. |
| `CuspOldColumn.coeff_form`, `numberField`, `coeff_mem_field`, `char_mem_field` | Fourier identification for a genuine dilation, the number field of the source and membership of its old coefficients and intrinsic character values. |
| `cusp_mem_span_intrinsic`, `finite_cuspidal_columns` | Restrict old/new spanning to the specified character and extract a finite list retaining newforms and old degrees. |
| `CuspBlockExpansion.col_numberField`, `col_coeff_mem`, `exists_actual_cuspidal_inventory`, `actual_inventory_at_fixed_place` | Produce the finite lists for the actual blocks and identify their algebraic columns over one finite extension of the fixed completion. |
| `exists_constituent_place`, `constituent_completion_finite` | Choose a prime over the fixed place and obtain the finite extension of completions. |
| `constituentValuation_extends`, `constituentValuation_complete`, `constituentValuation_integral`, `constituentValuation_maximal` | Normalize by the inverse local degree and compare the complete topology, the valuation ring and its maximal ideal. |
| `constituentComplexEmbedding_constituent`, `constituentComplexEmbedding_fixed` | The completion's complex embedding agrees with the specified embeddings of the constituent and fixed number fields. |
| `exists_eisenstein_coefficient_field` | Separate algebraic fact for the existing local Eisenstein block: the values and dilated divisor sums of a supplied pair lie in one number field. This is not used in the actual cusp inventory. |
| `block_span_of_inventory_labels`, `coordinates_of_block_span`, `joined_coordinates_of_block_spans` | The finite Fourier formulas give the block spans once the labels are represented. Descend exactly these spans and combine them via `evenVector_eval`. |
| `joined_vector_coeff_fixedRing`, `coordinate_match_of_joined_vector` | The resulting vector's evaluation is in the image of the fixed integral series and supplies the scoped coordinate premise for the constructed column and seed maps. |

`CuspOldColumn` labels a genuine normalized form and does not assert spanning. `CuspBlockExpansion` is produced by a theorem for each actual block; when used by `block_span_of_inventory_labels`, it asserts a finite linear combination for just that block (tex 9754–9764), without a model, joined seed or integral coordinates. `blockColumns` is a set; the explicit span premises refer only to the separate Fourier sequences, before forming the joined seed. The two constructor identities concern a linear column map and a seed prior to evaluation. No new leaf is introduced.

## Count and known issues

- Registered LEAF and GLUE counts are unchanged. The analytic existence of the fixed-set lists and their placement are now proved. The independent common model, its Galois and trace realization, and the per-set comparison on it remain GLUE.
- Tex 9663–9668: the inherited lattice issue remains. Integrality of a good Hecke image does not put it in the span of diamond translates alone. Use Hecke and diamond translates together.
- There is no general weight-two Eisenstein decomposition here. Such a theorem, if used for other forms, must treat the exceptional trivial pair by holomorphic level-raised combinations.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 8162–8167 | error | Inherited multiplier shorthand omits the base coefficient. |
| 8168–8182 | OK | The exact multiplier used by the inherited expansion. |
| 9497–9546 | gap filled | Rational translates and dilations of the actual moving source preserve cusp vanishing. |
| 9548–9555, 9618–9625 | gap filled | The unary Poisson transforms tend to zero at each cusp, since the linear factor kills their zero mode. |
| 9626–9646 | OK | Integer division and the fixed valuation ring precede reduction. |
| 9647–9648 | gap filled | The actual weight-two products are cuspidal and combine to the exact joined form. |
| 9649–9652 | gap filled | Actual finite lists, coefficient fields, finite completion and compatible algebraic embeddings. |
| 9650–9654 | unverified | The independent common presentation retaining old degrees and the attached representations have not been built. |
| 9655–9668 | unverified | No lattice or operator realization was instantiated here. |
| 9754–9764 | gap filled | Genuine intrinsic cuspidal source levels, old degrees and the correct character in the individual block expansions; the Eisenstein list can be empty. |
| 9764–9771 | unverified | Applying the existing model constructor to the actual inventory still needs the attachments and an independent presentation. |
| 9773–9861 | OK | The cuspidal local arguments read identified local factors and compare the Fourier shift on the new line. |
| 9862–9864 | OK | The ordered Eisenstein pair yields the divisor-sum shift whenever such a pair is supplied. |

## Verification

VERIFIED: All ten new modules under `ZInQKernel/Contrib/OneProof/RC/EvenJoin/` passed individual `lake env lean` checks. [The audit](../../scratch/rc-even-inventory/Audit.lean) covers all 47 new theorems, including private helpers. [Its output](../../scratch/rc-even-inventory/axioms.txt) contains only `propext`, `Classical.choice` and `Quot.sound`. No existing Lean file was modified.
