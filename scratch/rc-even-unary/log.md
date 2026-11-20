# Sizing and results

VERIFIED by reading `EvenExpansion/Assembly.lean` and `EvenExpansion/Unary.lean`: for `N₀ = (P.phaseData.N * conductor W.S)^3`, the exact target `EvenUnaryStageLaw P hS i j` takes `P.phaseData.η (-1) * (-1 : ℂ)^i.val = -1` and asserts a `DirichletCharacter ℂ (N₀ * j)` with value `P.phaseData.η n * (jacobiSym (-1) n : ℂ)^i.val * (kronecker (-(j : ℤ)) n : ℂ)` on each natural unit, and `HalfIntegralThreeHalves (N₀ * j) χ.toUnitHom (unaryFun (evenTypes W.S hS.1).Good P.phaseData.η i j)`. This last structure requires `MDiff`, transformation by `χ(d) * thetaMultiplier γ z ^ 3`, and bounded `cuspNorm (3/2)` for every `γ : SL(2, ℤ)`. `unaryFun good η i j z` is `∑' n, unaryCoeff good (fun k => η k) i j n * qParam 1 (z : ℂ)^n`; `unaryCoeff` at `n` selects a positive `k` with `n = j*k^2` and all prime factors good, and returns `η k * (jacobiSym (-1) k : ℂ)^i.val * k`, or zero if no such `k` exists. Only positive `j ∈ subscripts U` for a good finite set `U` are consumed.

| Piece | In the base (VERIFIED by reading) | Missing |
| --- | --- | --- |
| Shell and sieve (tex 9618–9622) | `unary_hasSum`, private `unary_shell`, `exists_unary_parity`, `good_iff`, `fixed_support`, `OldStageLaw.intResidues` | Reindex the convergent shell into positive terms, double using oddness of the periodic weight, and split into residue classes. |
| Weighted Poisson (tex 9623) | `OldStageLaw.line_inversion` is unweighted; Mathlib's `jacobiTheta₂'_functional_equation` proves the needed derivative identity. `HalfIntegral.jacobiTheta_rational_resum` and `jacobiTheta_at_cusp` handle the ordinary Gaussian. | Offset linear factor, weighted resummation, finite completion of the square, arbitrary cusp bounds. |
| Level and scalar (tex 9548–9555, 9624–9625) | `evenTypes`, `maskedLevel`, `unaryLevel_dvd`, `Jacobi.jacobiTheta_fourth_transform`; `OldStageLaw` word/cusp reduction is for a ternary grid. | Identify the relative scalar for the dilation and the sign from the cube of the theta multiplier; realize the corresponding character without changing the intrinsic level. This needs exact phases; a fourth-power identity alone does not suffice. |
| Transfer (tex 9626–9632, 9647–9655) | `includeUnary_mem`, `evenWeightTwo`, `evenExpansion`; the odd `BlocksPerU.UnaryStageLaw` is still an independent input, not a supplier. | Instantiate the unary argument and retain the existing moving and constituent-coordinate inputs. |

Known inherited error, VERIFIED from tex 8162–8176: the shorthand assertion about the integer multipliers omits the original reference coefficient; the following explicit formula restores it. The unary calculation uses neither formula.

VERIFIED by direct Lean checks: `Lines.lean` proves the weighted offset-line sum and Poisson identity, and `Resum.lean` proves the finite Fourier expansion, rational resummation and holomorphy of a general periodic weighted series. The derivative contribution is exactly one additional inverse Jacobi parameter. The offset term cancels.

Build setup: reusable artifacts came from the same revision. Lake rebuilt or replayed the low-level imports; a no-rebuild run for the full assembly dependency graph flagged stale artifacts in three upstream targets although the requested assembly object was present. Compiler invocations were locked. Two attempts to restart the setup overlapped at the Lake command level; the overlap was stopped, and direct checks thereafter are sequential.

VERIFIED by direct Lean check: `Finite.lean` proves that only the zero fiber modulo the coefficient period survives in the finite quadratic sum, identifies every even Fourier mode after completion of the square, and proves that the odd Fourier modes vanish. It uses the divisibility by four times the square of the period and makes no assumption about the weighted transformation or the ordinary theta phase.

VERIFIED by direct Lean checks: `Characters.lean` constructs the odd periodic coefficient character, proves the good-prime support is its unit support, and constructs the ordinary Jacobi factor as a character at any level divisible by `4j`. It also proves `4B²j ∣ B³j` by the level arithmetic. `Cusps.lean` proves holomorphy and uniform weight-(3/2) cusp bounds at every matrix for the periodic weighted series, before any scalar is evaluated.

VERIFIED by direct Lean checks: `Shell.lean` reindexes the actual `unaryFun` without changing coefficients and identifies it with half the two-sided series. `Transform.lean` proves the positive lower-left entry formula, including the phase before the ordinary Gauss sum is evaluated.

VERIFIED by direct Lean checks: `OddDenominator.lean` resums ordinary theta using an odd denominator, and `PrimeGauss.lean` derives the nondegenerate prime sum's scaling and square from Mathlib's multiplicative Gauss sums. These results use no assumptions about the shell.

VERIFIED by direct Lean checks: `Relative.lean` proves the complete weighted relative law at every matrix whose lower-left entry is divisible by `4B²j`, including upper translation and the lower unipotents. `OrdinaryPhase.lean` computes the absolute scalar `(-j/p)` when the lower-right entry is an odd prime `p`, with the ordinary theta multiplier cubed.

VERIFIED by direct Lean checks: `Assembly.lean` supplies the exact `EvenUnaryStageLaw` assuming only the scalar identity for two ordinary theta ratios; its transfer lemma supplies the weight-two form and the conditional lattice coefficient equality. The ordinary scalar assumption has no weighted data, cusp estimate, membership assertion, or constituent comparison.

VERIFIED by direct Lean checks: `Complete.lean` proves the ordinary comparison on the entire level group, using a right translation to a prime lower-right entry and treating triangular matrices by periodicity and negation. `evenUnaryStageLaw` proves the original proposition for every positive shell, and `evenExpansion_of_unary` removes the unary premise from the fixed even expansion. No hypothesis about the weighted law is left open.

VERIFIED: the scratch audit checks 72 public and private theorems. Their only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

VERIFIED resource stop for the extra dependency rebuild: load remained above the prescribed threshold, so no additional compiler was started. All direct module and scratch checks had already succeeded with compiled imports from the matching base revision. The full dependency rebuild is not claimed.
