# Sizing and results

VERIFIED: the requested old-stage merge succeeded; see `merge.txt`.

| Step | Existing input (VERIFIED by reading) | Missing work |
| --- | --- | --- |
| Mask and bridge | App E supplies the actual cusp form; `hiwForm_changeLevel`, `halfIntegralTwist`, and the square-covariant finite translation theorem already include cusp decay. `hiwForm_periodic_comp`, `hiwForm_mdiff`, and `hasSum_qExpansion` give period-one convergence. | Small: finite quadratic character projector or its equivalent DFT, support under level raising, normalization, bottom-right-entry evaluation and cusp boundedness in the second interface. The proved twist construction already gives all twists at one level and proves the character and cusp statements for sums with square-invariant coefficient multipliers. |
| Moving block | `Top`, `TL` and rational-translate cusp tools; tex supplies the two matrix calculations. | Substantial: exact theta-multiplier comparisons for dilation and the (U_{p^2}) conjugates, together with the permutation modulo (p^2) and q-series reindexing. No abstract operator facility in the imported half-integral files does these at level exponent one. |
| Unary | `unaryCoeff` and the ordinary Gaussian coset inversion, cusp and word computations. | Substantial: add the odd linear factor to the Poisson transform, then identify the scalar and conductor of the sieved unary form. The base level must be large enough for that character and the fixed support sieve. |
| Ordinary theta | `gridTheta_cusps` and `gridTheta_reference` for boundedness of the cube; nonvanishing and the one-variable Jacobi inversion and period formulas. | Small for the cusp field (cube root). The fourth-power transformation requires a separate calculation on `Gamma0 4`; the grid bound supplies no phase. |
| Weight two and transfer | `theta_product_modular`, `qExpansion_theta_product`, `commonCoeff_place` and `commonCoeff_complex`. | Small: retain separate characters at each intrinsic level, raise to a common Gamma1 space, assemble a period-one expansion, and inject through the given common place and the actual constituent coordinates. |

VERIFIED (tex 7898–7910, 7929–7934, 7813–7817): the manuscript's additive projection is on every integral frequency, including indices with square factors; only the subsequent phase comparison uses the full odd squarefree filter. The manuscript already describes the additive realization of the mask.

VERIFIED: `Jacobi.jacobiTheta_fourth_transform` compiles. The fourth power transforms in weight two on Gamma0(4). The proof uses Poisson inversion at the Fricke map, then centered Euclidean reduction by upper and lower unipotents. All 13 theorem audits are standard.

VERIFIED: `Projector.dual_orthogonality` compiles and its axioms are standard. The normalized sum over the dual of a finite group equals the indicator of the fixed label.

VERIFIED: `Operators.lean` compiles with seven standard theorem audits. Its actual dilation inserts zeros; its normalized finite additive average retains the multiples, including index zero. In particular `U_(p²) V_p` has the coefficients of `U_p`, and their difference with the weighted dilation has `Top` as its convergent expansion. The multiplier comparison is separate.

VERIFIED: `MaskCore.lean` passes both the Lake build and a direct Lean check. `quadraticProjection` cuts out a chosen unit label from an actual cusp form by a sum of quadratic twists at a single explicit level, retaining the lifted old character. The theorem gives the coefficients on units and nonunits at every index. Both theorem audits are standard.

VERIFIED: `Permutation.lean` passes its direct check. Its `upSquare_conjugation` supplies the residue permutation, integral entries, determinant, preserved level and bottom-right residue needed for the finite sum. All three audits are standard. The equality of the two theta multipliers is a separate calculation.

VERIFIED: `SeriesBounds.lean` passes its direct check. The positive square-shell series is absolutely summable for a period parameter of norm less than one when the coefficient norm is bounded by the shell parameter. The audit is standard.

VERIFIED: `Mask.lean` builds with five standard theorem audits. `evenMasked` supplies the normalized App E form at `(P.phaseData.N * conductor W.S)^3`, with the original character lifted, prime support in `W.S`, and the exact mask at every index. `evenMasked_reference` gives coefficient one at `D₀`; the two bridges give its convergent expansion in the half-integral interface.

VERIFIED: `Ordinary.lean` and `Unary.lean` build with six standard theorem audits. `ordinaryThetaLaw` supplies both the cusp bound and the fourth-power transformation. `unary_hasSum` gives convergence of the exact correction coefficients, and `exists_unary_parity` supplies the parity choice. The weighted unary Poisson comparison remains open.

VERIFIED: `Assembly.lean` builds with nine standard theorem audits. `moving_of_step` iterates the exact single-prime law on the series of the masked form. `evenWeightTwo` computes the coefficients of the actual assembled form at every index, with the unary characters lifted from their intrinsic levels. `evenVector_eval` gives the corresponding coefficient formula for separate basis coordinates. `evenExpansion` compares the two images of the divided series and transfers the equality through the complex embedding and the integral inclusion. Its coordinate comparison is with the actual form.

Build setup: the initial Lake import build was stopped when Lake's default compiler concurrency was noticed. Subsequent Lake builds use a compiler lock and host resource guard; the guard briefly held compilation and then resumed. Direct checks were sequential.

VERIFIED: the final Lake build completed, each of the ten new modules passed `lake env lean -j1`, and `lake env lean -j1 scratch/rc-even-expansion/Audit.lean` passed afterward. The 48 printed axiom sets are in `axioms.txt`; only `propext`, `Classical.choice` and `Quot.sound` occur. No protected statement or count file changed.
