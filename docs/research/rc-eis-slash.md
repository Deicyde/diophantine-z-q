# Modularity of the weight-two Eisenstein pair

For the ordered primitive pair with even product character, the explicit width-one series has a single constant term giving both the product-character slash law at the product level and the bounds at every other cusp. `pair_modularity` supplies `MissingModularity` and `pair_baseForm` supplies the exact `BaseForm`. No printed theorem or new analytic hypothesis is needed.

The construction subtracts the zero residue lattice from each translated residue lattice before summing. The two weight-two summands have the same leading term; their difference is of order `‖x‖⁻³` on the rank-two lattice. The absolutely convergent difference can therefore be reindexed under any integral determinant-one matrix. Changing the lift of a residue class does not change the corresponding iterated row sum. The weights are zero when the first coordinate is not divisible by the second conductor; otherwise they are `a(x₀/m₂) * b⁻¹(x₁)`, in the order inherited from EisForm. On the product-level `Gamma0` their pullback multiplies by `a(d)b(d)`. The correction from the common reference lattice cancels because the sum of those weights is zero when a factor is nontrivial.

The Lipschitz expansion of each nonzero row gives a geometric majorant uniform above any fixed positive height. The zero row is constant. Slash permutes the residue classes, so the same bound applies after moving any rational cusp to infinity. Regrouping by integer residue classes gives the ordinary row sums without interchanging the two infinite directions. Even parity combines the two signs of the first index, and the already proved primitive Gauss transform gives the ordered divisor sums. The scalar is
`(2 / (m₂ : ℂ)^2) * ((-2 * π * I)^2 * gaussSum b⁻¹ ZMod.stdAddChar)`.
The zero row divided by this scalar supplies the sole constant. The lattice subtraction, estimates, finite residue calculation, and transfer are on-the-spot (c).

## Statements

Names are in `ZInQ.Manuscript.RC.EisSlash`. Here `F_w` is the finite sum of residue differences at level `N`, with weights `w`, and `R_a(m,z)` is the inner row with residue `a` and outer index `m`. For ordered characters, `N = m₂ m₁`. A private statement is marked with an asterisk.

| Theorem | Statement | Supplies |
|---|---|---|
| `linear_eq_zero_iff`*, `summand_eq`* | The linear denominator at an upper half plane point vanishes exactly at the zero integer row; the weight-two summand is the square of its inverse. | Slash and cusps |
| `grid_injective`*, `linear_grid_bigO`* | A translate of the lattice scaled by nonzero `N` is injectively indexed; its inverse linear denominator is `O(‖x‖⁻¹)` on the cofinite filter. | Slash |
| `summable_lattice_diff` | At each upper half plane point the difference of two translates of the weight-two summand is summable over the full integer lattice. | Slash |
| `latticeDiff_add`, `latticeDiff_slash` | Differences add through an intermediate offset; weight-two slash by `g ∈ SL₂(ℤ)` right multiplies both offsets by `g`. | Slash |
| `summable_gridRow_inner`, `summable_gridDiff_prod`*, `latticeDiff_eq_rows` | The single row is summable, and the absolutely convergent lattice difference can be evaluated as the sum of the differences of inner rows. | Slash and cusps |
| `gridSeries_shift` | Shifting an offset by `N` times an integer vector leaves its iterated row sum unchanged. | Slash |
| `gridRow_eq_kernel`*, `rowKernel_neg`*, `rowKernel_zero`* | A row is the one-variable kernel at its integer first coefficient and second offset; simultaneous sign change preserves it; a zero first coefficient gives a constant. | Cusps |
| `positiveShift_im`*, `rowKernel_fourier`* | With positive first coefficient `k`, the shifted argument has imaginary part `k·im(z)/N`; its row is the weight-two Lipschitz series at that argument, scaled by `N⁻²`. | Cusps |
| `decay_lt_one`*, `summable_decay`*, `rowKernel_bound_pos`*, `gridRow_majorant`* | For `y>0`, `q=exp(-π y/N)<1` and `∑ n qⁿ` converges. Above height `y` this gives a summable geometric majorant for the rows, including the constant row. | Cusps |
| `summable_gridRows`, `gridSeries_bounded` | The outer sum converges for each upper half plane point; the iterated residue-class sum is bounded at infinity. | Cusps |
| `latticeDiff_eq_gridSeries_sub`, `latticeDiff_shift` | The lattice difference equals the difference of the two iterated sums; hence each offset can be shifted by a multiple of `N`. | Slash and cusps |
| `rowResidue_lift`, `exists_grid_of_residue_eq`, `rowResidue_vecMul` | The standard lift reduces to its residue; two equally reducing rows differ by a multiple of `N`; reduction commutes with right matrix multiplication. | Slash |
| `gridCombination_eq_rows`, `latticeDiff_residue_slash`* | Zero total weight cancels the reference sum, and slash permutes the lattice differences indexed by residues. | Slash and cusps |
| `gridCombination_slash`, `gridCombination_slash_scalar` | `F_w |₂ g` is `F` of the pulled-back weights; a scalar on the weights gives that scalar on the transformed function. | Slash |
| `gridCombination_bounded_slash` | `F_w |₂ g` is bounded at infinity for any integral determinant-one matrix. | Cusps |
| `rowWeight_grid`*, `characterWeight_on_row`, `rowWeight_transform`*, `characterWeight_pullback` | The integer row weight factors through reduction at `N`, and its pullback under `Gamma0(N)` multiplies by `a(d)b(d)`. | Slash |
| `pairNebentypus_value`*, `pairWeight_pullback` | On both orders of the actual pair, this scalar is the existing product nebentypus evaluated at the lower right unit. | `PairSlashLaw` |
| `summable_finite_prod`*, `sum_residue_rows` | Summability on each of finitely many residue classes gives summability on the integers and equality of the regrouped sums. | Both |
| `residue_vec`*, `grid_residue_vec`*, `weightedRow_on_residue`*, `gridCombination_eq_weightedRows` | Finite residue regrouping gives the periodic weighted integer row; when the total weight is zero, the iterated sum is exactly `F_w`. | Both |
| `splitResidue_val`*, `sum_residue_second`*, `sum_residue_first`*, `characterWeight_sum_zero` | The finite quotient and remainder indexing factors the residue sum into ordinary sums over the two character moduli; a nontrivial factor makes it zero. | Both |
| `rowWeight_mul`*, `weightedRow_mul`*, `weightedRow_zero`*, `weightedRow_even`*, `weightedRows_restrict`*, `weightedRow_positive`* | Only multiples of the second conductor contribute. The zero row is constant, parity makes the rows even, and each positive row equals the earlier character-weighted Lipschitz row times the first character and `m₂⁻²`. | Both |
| `orderedScale_ne_zero`, `pairScale_ne_zero` | The primitive Gauss normalization is nonzero in the generic and actual Fourier orders. | Both |
| `ordered_grid_fourier`, `inv_apply_neg_one`*, `ramified_complex_ne_one`*, `pair_grid_fourier` | After dividing by the stated nonzero scalar, `F_w` is the explicit series with its correct constant. The ramified primitive factor is nontrivial; inverse and original character agree at minus one, so product parity suffices in either order. | Both |
| `pair_checks_of_grid_eq` | The identity with `F_w` at a specific constant gives the slash law and the bounds for that same constant. | `PairSlashLaw`, `PairOtherCusps` |
| `missingModularity_of_gridFourier`, `baseForm_of_gridFourier` | The normalization identity gives a common constant for the two checks and the predecessor form. | `MissingModularity`, `BaseForm` |
| `pair_modularity`, `pair_baseForm` | For the actual complex-embedded primitive pair of even product parity, both checks hold for one constant and give the exact predecessor form. | `MissingModularity`, `BaseForm` |

`PairGridFourier E c` asks only for an equality of two given functions after multiplying by the explicit Gauss factor and choosing the constant. It does not posit a slash law, cusp bounds, holomorphy, primitive-character data or a modular form. It is used in the transfer at tex 9647–9654 and 9762–9764 and is proved by the row calculation for tex 9862–9864.

## Remaining hypotheses

| Exact input | Tex | Owner and size |
|---|---|---|
| The actual `CharacterPair D p`, embedding `D →+* ℂ`, `E.unram.IsPrimitive`, `E.ramified.IsPrimitive`, and `E.unram (-1) * E.ramified (-1) = 1`. | 9649–9654, 9762–9764, 9862–9864 | ELLIOT input: select the pair and identify its primitive characters and field for the occurring constituent. The parity is the compatibility at `-I` in weight two, not a field of the abstract `CharacterPair`. |
| Actual complex weight-two blocks, their source levels and degeneracies, the labeled Eisenstein old lines, and the coefficient transport to the common field and model. | 9647–9654, 9754–9771 | Block realization sibling for the actual blocks; ELLIOT input and constituent identification for the old lines and coefficient transport. These are downstream of the form construction. |

## Known issues

- Mathlib’s `EisensteinSeries/E2/Transform.lean` overview reverses the sign in its first displayed equation for `G2_S_transform`: the Lean identity has `+ 2πi/z` on the right when solved for `G₂(z)`. The subsequent slash equation agrees with the theorem. The same overview adds an extra separate `2ζ(2)` to the sum defining the `G2Term` expression; `G2_eq_tsum_G2Term` has no such separate constant. Neither display is used in this proof.
- The level-one trivial/trivial pair is quasimodular. The nontrivial-factor hypothesis in the general residue calculation is necessary for the common reference term to cancel. It follows from primitivity of the ramified factor in the actual pair.
- Inherited issue at tex 9660–9668: integrality of a good Hecke image does not put it in the span generated by diamonds alone. The coefficient lane uses closure under both operators. No new manuscript error was found.

## Manuscript check

- Tex 9647–9648 — unverified: the actual products and their block modularity are with the block realization lane.
- Tex 9649–9654 — gap filled: the primitive Eisenstein form needed for the characteristic-zero constituent is holomorphic, has the correct nebentypus, and is bounded at all cusps. The actual old-line labels remain inputs.
- Tex 9754–9761 — unverified: source levels and their distinction before raising the level are block inputs.
- Tex 9762–9764 — gap filled: for the occurring primitive pair, the constructed form has the stated product level and character. Realization of all labeled constituents is downstream.
- Tex 9765–9771 — unverified: the assignment to the common constituent decomposition is outside this lane.
- Tex 9862–9864 — gap filled: the modular function is identified with the exact ordered positive divisor sums and one compatible constant; the Galois and local shift comparison is inherited.

## Verification

All eight files under `ZInQKernel/Contrib/OneProof/RC/EisSlash/` compile individually with `lake env lean -j1`, run serially. The 65 `#print axioms` audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The final checks reported no warnings or errors.
