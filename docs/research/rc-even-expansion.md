Scoped stop: for one fixed good operator set `U`, Lean proves `evenWeightTwo` and `evenExpansion` conditionally on two half-integral comparisons. The first is the transformation of the actual fresh-prime operator at level `M * p`; the second is the weighted unary Poisson law for one shell at level `N₀ * j`. The App E mask `evenMasked`, both ordinary theta laws, the moving Fourier and finite conjugation calculations, and convergence of the unary expansion are proved without those inputs.

The assembly forms the ordinary theta products, retains the intrinsic and pulled-back unary characters, and computes the divided sum at **all** indices. The final transfer uses a compatible complex embedding of the chosen coefficient place and `hcoord`, the equality between the constituent coordinates and the Fourier coefficients of this actual weight-two form. It proves the required lattice identity at every positive index. This is a statement for one fixed `U`; the budget still needs the same place and a constituent construction for all its tested sets.

## Known issues

**Manuscript error (tex 8162–8167, inherited).** The proposed `b₀` is `a(D)`, so the assertion that the `bᵣ` are integer multipliers omits a factor of `a(D)`. The explicit formula at tex 8168–8176 uses the correct factorization. No expansion identity here uses the shorthand.

The mask in tex 7898–7910 and 7929–7934 applies to **every** integral Fourier frequency, including indices with square factors. This differs from the domain of the phase comparison: tex 7813–7817 and 8136–8155 use the full odd squarefree filter for (D). The all-index projector in `EvenSource.sievedCoeff` matches the scope of the manuscript's support projection.

## Sizing

The import and proof inventory is in [the sizing log](../../scratch/rc-even-expansion/log.md). The mask uses a finite character projector, a common-support level and the identification between the two half-integral interfaces. The tree already has a uniform twist at the cubed level. The moving formula separates Fourier reindexing and integral conjugation, which are small, from the exact theta multipliers and cusp comparison for the dilation and the additive translates at fresh level exponent one, which are substantial. The ordinary theta cusp field follows from bounding its cube. Its fourth-power field follows from the Jacobi inversion and period formulas and reduction by upper and lower unipotents in `Γ₀(4)`. The unary comparison still needs an inversion formula for the odd linear factor and the identification of its character at the intrinsic level. The unweighted Gaussian identity alone does not give that comparison.

The finite arithmetic and ordinary theta calculation are provenance (c). The only literature locators carried over for the remaining half-integral arithmetic are Shimura, *On modular forms of half integral weight*, §1 for the multiplier and Lemma 3.6 for twists: **UNVERIFIED** for this check. The Lean projector uses the already proved translation-twist construction.

## Lean statements

Write `N₀ = (P.phaseData.N * conductor W.S)^3`, let `U` be one finite set of good primes, and write `m = N₀ * ∏ p ∈ U, p`. The conditional analytic inputs are independent of the constituent model. `MovingStepLaw M p χ η g` says the actual difference `U_(p²)(V_p g) − η • V_p g` satisfies the half-integral law at `M * p`, with character `χ(n) (p/n)` on every unit. `EvenMovingSieveLaw P U` packages the iterated law for the moving Fourier series and its prescribed character at `m`. `EvenUnaryStageLaw P hS i j` says, in matching parity, that the convergent function `unaryFun` at shell `j` satisfies the half-integral law at `N₀ * j`, with character `η(n) χ₋₄(n)^i (−j/n)` on units. Neither asks for a weight-two coefficient identity or a local Fourier coefficient.

| File | Theorems and conclusions |
| --- | --- |
| `Jacobi.lean` | `lower_add`, `Tmul_entries`, `lowerMul_entry` give the unipotent identities; `centre` gives centered division. `transform_characterization` and `mem_thetaStabilizer` identify the weight-two slash relation, `T_mem_stabilizer`, `neg_one_mem_stabilizer`, `lower_one_mem_stabilizer`, `lower_mem_stabilizer`, `triangular_mem` supply the stabilizing matrices, and `stabilizer_of_c` reduces the lower-left entry. `jacobiTheta_fricke_fourth` computes inversion at `−1/(4z)`; `jacobiTheta_fourth_transform` gives the weight-two transformation on `Γ₀(4)`. |
| `Projector.lean`, `MaskCore.lean` | `dual_orthogonality` identifies the finite character average with the indicator of one label. `squareTwist_sq` makes every twist quadratic. `quadraticProjection` realizes this projector with a fixed character at the cubed level, with the required scalar and zero off the chosen unit class. |
| `Mask.lean` | `threeHalves_of_cusp` and `hasThreeHalves_of_cusp` give the analytic and Fourier bridges. `evenMasked` produces the fixed support cusp form with `hiwCoeff G n = P.sievedCoeff n` for every `n`; `evenMasked_reference` gives `P.sievedCoeff P.D₀ = 1`; `evenMasked_expansion` gives the same series in `HasThreeHalvesExpansion`. |
| `Operators.lean` | `up_translation`, `qParam_dilate` and `qParam_undilate` describe the finite translate sum and change of Fourier parameter. `series_Vp`, `series_Up` and `series_Up_sq_Vp` give the Fourier coefficients of the actual functions. `movingOp_series` computes the coefficients of their difference as `Top p η a`, including index zero. |
| `Permutation.lean` | `fractionalPermutation` proves bijectivity wherever the denominators are units. `upSquare_permutation` supplies the permutation and integral numerator quotient; `upSquare_conjugation` gives determinant one, level divisibility and unchanged bottom-right entry modulo the level. |
| `SeriesBounds.lean`, `Unary.lean` | `summable_squareShell` bounds any positive shell with coefficients of norm at most the shell parameter. `exists_unary_parity` selects a sign so that the unary character is odd. `unary_shell` evaluates the exact coefficient on a positive shell with its good-prime sieve; `unary_hasSum` gives the convergent expansion of `unaryFun`. |
| `Ordinary.lean` | `ordinaryTheta_cusps` bounds theta at every cusp, `ordinaryTheta_fourth` computes the fourth power of its multiplier on `Γ₀(4)`, and `ordinaryThetaLaw` combines the two. |
| `Assembly.lean` | `moving_nil` supplies the moving law for the empty set from the masked source; `moving_of_step` iterates the single-prime law. `subscripts_dvd` and `unaryLevel_dvd` give the needed divisibility. `includeUnary_mem` records the lifted diamond character in the common space. `weightTwoBlock` supplies the actual theta product with the specified diamond character and its convolution. |
| `Assembly.lean` | `evenWeightTwo` forms `f = 2^(-(P.δ + U.card + 1)) • (fB − ∑ⱼ raw(j) • fJ)` in weight two at level `m`, using the included unary forms. Every coefficient of `f` equals `timesTheta (halfDivided Good η P.sievedCoeff P.δ i U.toList)`. `evenVector_eval` evaluates the same combination in a constituent basis, allowing the depth shift at the coefficient place. `evenExpansion` transfers the identity to `A.coeff n (X.F U)` for every `n ≠ 0` via `κ.comp C.eK = C.eC` and the coordinates of this `f`. |

## Count

VERIFIED against `docs/one-proof/OPEN.md`: strict and strictest for the H part are both **5 published / 24 glue → 5 published / 24 glue**. Including the separate manuscript hypothesis gives **5 / 25 → 5 / 25**. This is internal RC glue; no open-statement row or classification changes.

## Manuscript check

- Tex 7793–7808, 7813–7817 — OK: the phase statement is on the full odd squarefree filter; the normalized form has a wider all-index expansion.
- Tex 7898–7910, 7929–7934 — OK: the support idempotent acts on every integral frequency, including non-squarefree ones; the chosen unit squareclass is stable under unit squares.
- Tex 8099–8103 — gap filled: use the existing finite additive translation twist at its uniform cubed level, and average the quadratic twists to project to the prescribed unit class.
- Tex 8146–8155 — OK: the later sieve deletes indices by coprimality. Its effect on the phase statement remains restricted to the retained squarefree indices. No later exclusion is imposed on the fixed source in this task.
- Tex 8162–8167 — error: the recurrence shorthand omits the base coefficient in the normalization; the explicit factorized recurrence follows at tex 8168–8176.
- Tex 9497–9546 — unverified: the residue permutation, integral conjugation and Fourier calculation have separate proofs; the single-prime half-integral transformation at exponent one still requires the stated multiplier comparisons and cusp control.
- Tex 9548–9555 — unverified: the modularity of the initial sieved odd-character unary series and of each dilate is included in the intrinsic-level unary comparison.
- Tex 9618–9625 — unverified: convergence of the exact even unary series is separate from the weighted Poisson transformation with the asserted character and level.
- Tex 9626–9632 — OK: the matching-parity combination uses division by integer two after the unary subtraction; the even-budget proof handles the divisibility.
- Tex 9647–9648 — gap filled: the fourth-power transformation follows from Jacobi's formulas; add the all-cusp bound and use the existing theta product with its exact convolution.
- Tex 9649–9655 — unverified: the constituent model must realize the actual form in the given common place, with the separate block characters.
- Tex 9754–9760 — unverified: retaining intrinsic block levels is part of the assembly; the local constituent assertions are separate.

## Verification

VERIFIED: the serial Lake build completed for `EvenExpansion.Assembly` and `EvenExpansion.Permutation`. All ten new modules then passed direct `lake env lean -j1` checks, as did [the scratch audit](../../scratch/rc-even-expansion/Audit.lean). The [48 printed axiom sets](../../scratch/rc-even-expansion/axioms.txt) use only `propext`, `Classical.choice`, and `Quot.sound`. The two half-integral comparisons occur as hypotheses in the theorem types; they are not axioms or new printed-form leaves.
