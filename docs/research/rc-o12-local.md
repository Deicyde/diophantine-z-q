# Cuspidal local blocks for (O.12)

`O12Local.localInput` supplies `O12.LocalInput` from the cuspidal data and a separate Eisenstein sector, on the same `GaloisConstituentModel.ρ` and coefficient family as `O12.inputs_of_theta`. In a ramified cuspidal block the bad-prime Hecke sum and arithmetic Frobenius on the unramified Galois line both act by $\sqrt p\,\mu_1(p)$. The normalized induced vector, its $BK_0(p)$ support and lower-right character, the stability of its line under the sum, the value of the sum, the two duals, the inertia signs, the multiplicity copies, and the Fourier shift from the named Whittaker comparison are proved. On the old cuspidal sector the Galois action on inertia is trivial; the operator can mix the retained old coordinates.

This is a conditional assembly of the actual local data, not a construction of adelization, local reciprocity, or the manuscript's theta forms. The remaining analytic comparison is the finite Whittaker realization of those forms, including its $a_n/n$ normalization. The smallest slice used is the two positive coefficients at $1,p$, the local translate identity at (1), the integral unipotent translations there, and right invariance at the away components of $a(p)$. The only representation results quoted as PRINT are Casselman and Carayol. An Eisenstein sector and its coefficient shift remain with the sibling task.

## Statements

All names below are in `ZInQ.Manuscript.RC.O12Local`. The support masks and the finite matrix bookkeeping without separate manuscript locators have provenance (c).

| Lean theorem | Statement and interface use |
| --- | --- |
| `heckeSum_at_one` | In a normalized induced model, $H_pv(1)=p\mu_1(p)\omega_p(p)^{1/2}v(1)$, by evaluating each upper triangular representative. Used for `newLine`. |
| `newvector_at_one` | In the complex normalization with $v(1)=1$, the value is $\sqrt p\,\mu_1(p)$, using the actual (p)-adic norm. Right covariance and support are not needed once evaluating this sum at (1). Used for `newLine`. |
| `heckeSum_at_one_normalized` | The same computation in the common coefficient field, with the reciprocal of the normalized half-modulus at (p) as the chosen square root. Used for `newLine`. |
| `central_mem_atK1`, `central_trivial_of_level` | A central congruence unit gives a $K_1(p^n)$ element and acts trivially on a nonzero fixed vector. Used for `newLine`. |
| `conductor_bounds`, `conductor_one` | $a(\chi)\leq a(\pi_p)\leq n$; hence $a(\pi_p)=1$ at a level of exponent at most one with primitive character. Used for `newLine`. |
| `ordered_principal` | Excludes both special cases and the supercuspidal case, orders the principal-series characters with conductors (0,1), and keeps their product equal to the central character. Used for `newLine`. |
| `newspace_one` | The allowed level already has exponent exactly one and its fixed space has dimension one. Used for `newLine` and the count at (p). |
| `switchMatrix_conjugation`, `switchMatrix_atK0`, `switchMatrix_atK1` | The conjugation by $h_{p^n}$ swaps the diagonals and preserves $K_0(p^n)$ and transports the $K_1(p^n)$ condition; at $n=1$ this is the change of character convention in the text. Used for the normalization of `newLine`. |
| `lower_atK1`, `upper_atK1`, `swap_diagonal` (private) | The lower and upper factors used in the two cells satisfy the level test; the Weyl element swaps the two diagonal factors. Used to normalize `newLine`. |
| `factor_in_open_cell`, `InducedModel.supported_BorelK0`, `right_equivariantK0` | The open cell has the explicit Borel and level factorization. The fixed function vanishes off that cell and transforms on the right by the lower-right character. Used to normalize `newLine`. |
| `InducedModel.vanishes_on_weyl`, `support_and_evaluation`, `normalized_generator` | The ramified inducing character forces vanishing on the other cell. A fixed vector whose value at (1) vanishes is zero; consequently the generator can be scaled to value (1). Used for `newLine`. |
| `red_zero_iff`, `permute_residues` (private), `level_one_permutes` | Reduction detects divisibility by (p); a nonzero affine slope gives a permutation, and $g\,\mathrm{rep}(b)=\mathrm{rep}(s(b))k_b$ with $k_b\in K_1(p)$. Used for `newLine`. |
| `weilAt_le_decomposition`, `CarayolPrincipal.character_lines`, `weil_values` | The Weil subgroup lies in the actual decomposition group. In one basis the two decomposition characters are the inverses of the compared dual characters; their Weil values are $\mu_j(\mathrm{rec}(w))^{-1}\omega_p(\mathrm{rec}(w))^{1/2}$. Used for `newLine`. |
| `CarayolPrincipal.on_inertia`, `on_frobenius` | The first line is trivial on inertia; the second is the prescribed quadratic character. Arithmetic Frobenius on the first is $\sqrt p\,\mu_1(p)$, independent of the unit in its reciprocity image. Used for `newLine`. |
| `localHecke_preserves`, `localHecke_on_line`, `RamifiedFactor.line` | The coset permutation preserves the fixed line. Evaluating its operator at (1) gives the same scalar as Frobenius in a common basis with inertia diagonal (1,-1). Supplies `newLine`. |
| `RamifiedLine.on_copy`, `CuspidalData.diagonalEntry_eq`, `up_on_ramified`, `up_on_copy` | Every coordinate attached to the same cuspidal factor gives the same operator on a copy of its newvector. Supplies the scalar part of `newLine`. |
| `CuspidalData.diagonalEntry_eq_zero`, `old_unramified` | The ramified operator has zero entries outside its sector; on an active unary block omitting (p), $\rho(\tau)=1$. Supplies `preserves_ramified` and `old`. |
| `mask_apply`, `mask_supported`, `split_supported` | Coordinate projection, support intersection, and splitting of a vector supported in two disjoint sectors. Used in `supported`, `preserves_ramified`, and `UpAtOne`. |
| `away_diagonal_atK1`, `WhittakerComparison.coeff_shift` | Each away component of $a(p)$ passes every (K_1\) level test. The finite (p)-sum then gives $p\cdot a_p/p=a_p$ at index one. Supplies `UpAtOne`. |
| `Sector.scalar_eq_p_coeff` | The scalar on a supported eigenvector normalized at coefficient one is its coefficient at `p`. Consequence of `UpAtOne`. |
| `cuspidal_upAtOne`, `combine_upAtOne`, `localInput` | The cusp shift holds on the cusp sector, the two sector shifts sum on the active space, and staging the combined local data yields `O12.LocalInput`. |

`CuspidalData.sector` determines `active` from the occupied cuspidal coordinates and `ramified` from the theta block and unary blocks with $p\in J$. It gives the local operator, `old`, `newLine`, and preservation of the active and ramified subspaces. `combine` supplies every field of the existing `O12.LocalBlocks`, including `supported` from the support of the actual form in the disjoint union.

## Named inputs

| Input | Kind and manuscript locator |
| --- | --- |
| `RamifiedFactor.occurs`, `level_le`, `central`, `char_one`, `quadratic`; `CuspidalData.kind`, `factor`, `coordinate`; `Stage.support` | ELLIOT / data of the actual block construction, tex 9754–9771 and 9799–9811. The constituent occurs in the specified level, with the indicated central character and absolute inertia restriction. The repeated coordinates refer to the same characteristic-zero newform factor. |
| `RamifiedFactor.exact_conductor`, `CasselmanCases` | Definition of the least level with a nonzero fixed vector and PRINT, Casselman, Theorem 1, pp. 302–306 (UNVERIFIED), tex 9799–9809. The principal-series branch has the normalized induction model, its central character product, and the sum of inducing conductors. The special and supercuspidal bounds are stated separately. |
| `CasselmanOldspace` | PRINT, Casselman, Corollary p. 306 and Theorem 4 p. 313 (UNVERIFIED), tex 9859–9861. At exponent (n) and conductor (c), the fixed-space dimension is $\max(0,n+1-c)$. |
| `PrincipalInterchange` | ELLIOT, tex 9825–9827. Only the order change from characters of conductors (1,0) to (0,1) is needed. No general intertwining theory is introduced. |
| `ReciprocityAt`, `halfMod`, `half_units`, `half_uniformizer` | Convention/realization used by the Carayol print, tex 9773–9797, 9816–9817 and 9857. The Weil reciprocity map sends inertia into units, and the chosen arithmetic Frobenius lift to inverse uniformizer times a unit. The same transported half-modulus is used in both calculations. |
| `CarayolPrincipal`, `CarayolUnramified` | PRINT, Carayol, §§0.3–0.7, Théorème A, pp. 409–411 (UNVERIFIED), tex 9778–9797; unramified case used for the source forms in tex 9757–9760. The principal case states the zero-monodromy compatibility using the two characters extended to the decomposition group, with the literal formula on the Weil subgroup. It compares the dual of the *existing* `ρ` with the parameter for the automorphic contragredient. The representation existence print is not repeated. The old case is the same unramifiedness used in the shared constructor, stated for the single prime-to-(p) source form. |
| `CuspidalData.oldUp` | ELLIOT / operator data, tex 9757–9759, 9841–9856, 9857–9861. This is the actual old-space operator, confined to those coordinates by the sector construction. `LocalBlocks` needs no old-space eigenvalue. |
| `WhittakerComparison` | ELLIOT, tex 9841–9856, **no citation given**. The finite evaluations of the actual adelized form and the translate sum must agree with its Fourier coordinates, in the normalization $W_\infty(a(y))=y e^{-2\pi y}$. The type records the needed additive and right level equivariance and the equality $W_f(a(n))=a_n/n$ at the full finite argument. The coefficient shift itself is proved, not included in this input. |
| `Stage.eisenstein`, `eisenstein_shift` | Named sibling input, tex 9862–9864. Supplies a disjoint Eisenstein sector with its own (p)-to-one coefficient shift. No Carayol theorem is applied to these coordinates. |

## Known issues

- The printed locators are transcribed from the manuscript and are UNVERIFIED on this run. As noted in `docs/research/r17-rebase.md`, a conductor equality is a consequence of local compatibility and the newform conductor calculation, not the statement of Carayol's Théorème A. This contribution keeps the conductor argument separate.
- A Frobenius element can be changed by inertia. The normalization at tex 9784 fixes the reciprocity value modulo units for an arbitrary lift. The proof does not assign the same second Frobenius eigenvalue to different lifts.
- The finite-place argument at tex 9848–9854 omits the away components from its notation. Their level condition is proved here. For the actual forms a future proof of `WhittakerComparison` would need cuspidal adelization and its global Whittaker expansion with the named real normalization, neither currently available in the shared local API. That is a separate formalization of the automorphic and analytic comparison; the two evaluated coefficients and the three equivariance identities listed above are its smallest interface here.
- The construction works over a coefficient field containing the chosen realizations. It checks the equality of the two scalars there. Algebraicity over `ℚ` for the actual form additionally uses its normalized algebraic Fourier coefficients (the scalar is its coefficient at (p)); no algebraicity claim about arbitrary constituents over an arbitrary field is made here.
- The inherited ambient good-prime issue of `docs/research/rc-o12.md` is unchanged. A single ambient `avoid` set cannot establish every formwise good Hecke comparison. This contribution specializes the local input of the existing theorem and does not build the shared model.
- No manuscript error was identified. The missing away-component justification is a gap in the displayed argument, not a change to its formula.

## Manuscript check

- Tex 9754–9761 — OK: ramified and old cuspidal coordinates are tagged separately; the prime-to-(p) source has trivial inertia by the unramified comparison.
- Tex 9762–9771 — OK: the construction uses the existing characteristic-zero constituent representation and retains multiplicity coordinates; the common model itself is input.
- Tex 9773–9791 — unverified: the Satake normalization and the precise Carayol locator and compatibility are used as stated by the manuscript.
- Tex 9792–9797 — gap filled: both duals are explicit and the unramified character removes the unit ambiguity for arbitrary arithmetic Frobenius. The good-prime polynomial is background from the base comparison.
- Tex 9799–9801 — gap filled: a central congruence unit must fix a nonzero level-fixed vector; the definition of representation conductor gives the other bound.
- Tex 9802–9806 — unverified: the cases and bounds are the Casselman printed-form input.
- Tex 9807–9811 — gap filled: the nonprincipal cases are excluded, the conductor sum gives (0,1), and the central product and quadratic inversion give the claimed inertia character.
- Tex 9813–9824 — OK: the finite induction equation uses the lower-right convention, and the conjugation formula proves the switch. The induced function has the lower-right character by factoring off the central scalar.
- Tex 9825–9827 — unverified: the uncited principal-series interchange is a named input only in the order used.
- Tex 9828–9835 — gap filled: computed the residue-class permutation proving that the displayed finite sum preserves the fixed space. The finite sum is taken in the stated Haar normalization.
- Tex 9836–9840 — gap filled: the function vanishes outside \(BK_0(p)\), evaluation at one normalizes a nonzero fixed vector, and Lean evaluates the (p) equal terms.
- Tex 9841–9849 — gap filled: the existing finite Whittaker sum gives the (p)-factor; the other finite components of $a(p)$ pass the level test.
- Tex 9850–9854 — unverified: the uncited adelization and $a_n/n$ normalization are the ELLIOT input.
- Tex 9855–9857 — OK: the coefficient comparison identifies the finite operator; its scalar equals Frobenius on the unramified Galois line. On a normalized eigenform the scalar is its coefficient at \(p\).
- Tex 9858–9861 — gap filled: evaluating the Casselman count at the allowed level gives one local dimension, with the same scalar on every other-prime copy.
- Tex 9862–9864 — unverified: deferred to the Eisenstein sibling.
- Tex 9866–9873 — OK: taking the existing pair and the common basis produces the two requested matrices and the bad-prime scalar.

## Verification

All nine modules compile with `lake env lean -j1` on the pinned toolchain, one Lean invocation at a time. The 47 new theorems, including private helpers, each print only `propext`, `Classical.choice`, and `Quot.sound`. The changed imports of the exact base revision were rebuilt in dependency order. No base source files were edited.
