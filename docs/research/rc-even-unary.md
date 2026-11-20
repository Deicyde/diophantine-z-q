# Intrinsic unary theta transformation for the even expansion

**Result.** The unchanged `EvenExpansion.EvenUnaryStageLaw P hS i j` holds for every positive shell $j$, in particular every $j\in\mathrm{subscripts}(U)$ used by the even expansion. The provider is `ZInQ.Manuscript.RC.EvenUnary.evenUnaryStageLaw` in [Complete.lean](../../ZInQKernel/Contrib/OneProof/RC/EvenUnary/Complete.lean). It proves the law for the actual convergent function at $N_0j$, where $N_0=(N\operatorname{conductor}(W.S))^3$, with character $\eta(n)\chi_{-4}(n)^i(-j/n)$ on every unit. `evenExpansion_of_unary` supplies a weight-two form with the prescribed coefficients in the existing common space and passes its positive-index coefficient identity to the fixed-place constituent under the existing coordinate hypotheses.

**Remaining inputs.** The unary law has no remaining analytic input. The wrapper still uses the good-prime condition, the matching parity selected by the existing `exists_unary_parity` (tex 9618), and the following two inputs:

| Input | Manuscript | Owner |
| --- | --- | --- |
| `EvenMovingSieveLaw P U`, supplied by iterating the fresh-prime `MovingStepLaw` | Tex 9497–9546 | The separate moving proof |
| A compatible complex embedding of the fixed coefficient place and agreement of the constituent coordinates with the actual assembled form | Tex 9649–9655 | The lead, in the constituent construction |

There is no new literature leaf. The sole new auxiliary proposition, `OrdinaryDilationComparison`, is the explicit identity $(cz+d)J_j=((-j)/d)J_1^3$ with the Kronecker symbol as coefficient and the ratios $J_j=\theta(j\gamma z)/\theta(jz)$. It supplies only the ordinary theta scalar in tex 9548–9555 and 9624–9625. It is strictly narrower than the unary stage law: it does not involve the weighted series, fixed-support sieve, its parity, holomorphy, cusp bounds, or modular-form membership. `ordinaryDilationComparison_proved` discharges this auxiliary premise in the exported provider.

Write $B=N\operatorname{conductor}(W.S)$, where $N=P.\mathrm{phaseData}.N$. The old-support sieve extends the odd character $\eta\chi_{-4}^i$ from the old level to $B$, taking the value zero on nonunits. Reindexing the convergent square-shell series gives half the bilateral weighted theta series, evaluated at $2jz$. Weighted Poisson summation for a shifted line follows from Mathlib's derivative of the two-variable Jacobi functional equation. The shift cancels out of the linear factor. Grouping by finite residue classes then gives the weighted sum at every rational cusp. This is the weighted counterpart of `OldStageLaw.line_inversion`.

For positive lower-left entry, the finite phase calculation kills the odd dual indices and the even ones give the original character and Gaussian after completing the square. This gives the law relative to the ordinary theta ratio at dilation $j$ whenever $4B^2j$ divides the lower-left entry. Periodicity treats translation, and negating a matrix treats a negative lower-left entry; the positive-entry calculation includes the lower unipotents at the level. No generating-set assertion about $\Gamma_0$ is needed. Since $4\mid B$, the desired level $B^3j$ is divisible by $4B^2j$. The estimates at cusps apply even to matrices outside the level: resummation bounds the series by a constant times $|cz+d|^{3/2}$ uniformly as the imaginary part tends to infinity.

At the scalar step the comparison is between two ordinary Jacobi theta ratios, with dilations $1$ and $j$. For positive odd lower-right entry, ordinary Poisson summation at that denominator separates the common analytic factor and a finite quadratic sum. When that entry is prime, scaling the sum gives $(j/d)$, and squaring gives $(-1/d)d$. The analytic factor squared is $(cz+d)/d$. Consequently the relative scalar is $(-j/d)$ when the law is expressed using the **cube** of the theta ratio. For nonzero lower-left entry, Mathlib’s Dirichlet theorem supplies an odd prime in the residue class of the lower-right entry modulo the absolute lower-left entry. Right translation moves the matrix to that prime without changing the comparison; periodicity transports both ratios and the character is unchanged. For zero lower-left entry, the ratios are 1 by periodicity. Comparing a lower unipotent with its negative gives the character value at −1.

## Known issues

- Inherited manuscript error, tex 8162–8167: the shorthand assertion about integral multipliers leaves out the reference coefficient. The explicit recurrence and product in tex 8168–8176 supply it. No step of this proof uses that shorthand.
- The surrounding project notes locate the traditional theta multiplier in Shimura, *On modular forms of half integral weight*, §1 (UNVERIFIED here). The proof uses the named Lean Jacobi, finite character, and Gauss sum results directly. No new error in the checked unary passage was found.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 8162–8167 | error | The recurrence shorthand omits the original reference coefficient; the later explicit formula supplies it. |
| 9497–9546 | unverified (separate moving proof) | The unary proof does not supply the moving operator input. |
| 9548–9552 | gap filled | The old-support sieve is exactly the unit restriction of the coefficient character, and $V_j$ is evaluation at $jz$. |
| 9552–9555 | gap filled | The proved intrinsic level contributes only $j$ to the old-support level; the existing product with ordinary theta introduces no enlargement. |
| 9618–9622 | OK | The parity condition and the positive square-shell series are the hypotheses and function of the Lean statement. |
| 9623 | gap filled | The weighted derivative identity, residue expansion, holomorphy, and cusp bounds supply the unary form. |
| 9624–9625 | gap filled | The power of the ordinary theta multiplier is fixed by the exact phase; the character values are proved on all units. |
| 9626–9632 | OK | The existing assembly uses the same unary shell in (O.11); its integrality is separate from the Poisson step. |
| 9647–9649 | OK | The existing `evenWeightTwo` multiplies the blocks by ordinary theta and supplies the stated $q$-coefficients. |
| 9649–9655 | unverified (outside this proof) | Choosing and matching a fixed constituent over the coefficient field is retained as the compatible embedding and coordinate input. |
| 9754–9760 | unverified (outside this proof) | The local constituent analysis uses the levels and characters but is downstream from their construction here. |

## Lean results

| File | Theorems (including helpers) | Input discharged |
| --- | --- | --- |
| Lines.lean | `jacobiDerivative_ne`, `linearTheta_hasSum`, `jacobiDerivative_eq`, `linearLine_hasSum`, `linearLine_eq`, `linearLine_poisson`, `linearTheta_periodic` | The first derivative, summability, cancellation of the offset in Poisson inversion, and translation for one line. |
| Resum.lean | `weightedTheta_hasSum`, `jacobiTerm_addChar`, `weightedTheta_fourier`, `weightedTheta_periodic`, `rationalArgument_im`, `weightedTheta_rational_resum`, `norm_linearTheta_le`, `weightedTheta_differentiableAt` | The finite Fourier decomposition of the periodic weight, rational resummation, a uniform estimate, and differentiability. |
| Finite.lean | `phase_reduction`, `quadratic_zero_residue`, `weightedQuadraticFourier_even`, `weightedQuadraticFourier_odd` | The surviving residue fiber and the exact even and odd modes. |
| Characters.lean | `changeLevel_int`, `character_pow_unit`, `sievedCharacter_odd`, `sievedCharacter_at_unit`, `good_factors_iff_coprime`, `coprime_supportModulus`, `four_mul_sq_dvd_cube`, `odd_unit`, `jacobiUnitHom_one`, `jacobiCharacter_at_unit` | Oddness, character values, exact support, the level divisibility, and the Jacobi factor at natural units. |
| Shell.lean | `shell_term`, `shell_reindex`, `jacobiTerm_shell`, `unaryFun_eq_weightedTheta` | Exact square-shell coefficients, reindexing, and identification of the actual positive series. |
| Transform.lean | `weightedTheta_rational_modes`, `tsum_even_odd`, `weightedTheta_at_cusp` | Passage from residue classes to Fourier modes and weighted relative comparison at positive lower-left entry. |
| Cusps.lean | `weightedTheta_holo`, `coe_action`, `im_neg_inv`, `neg_inv_neg_inv`, `norm_poisson_factor`, `cusp_positive`, `cusp_zero`, `weightedTheta_cusps` | Holomorphy and weight-3/2 cusp bounds, with the zero and positive lower-left cases proved separately. |
| Relative.lean | `coe_action`, `im_positive_mul`, `relative_pos`, `relative_zero`, `weightedTheta_relative` | Full group law relative to the unweighted theta ratio, using translation, positive-entry resummation, and sign. |
| OddDenominator.lean | `ordinaryTheta_odd_denominator` | Ordinary theta resummation at a positive odd denominator after completing the square. |
| PrimeGauss.lean | `primeQuadraticFourier`, `primeGauss_scale`, `primeGauss_sq`, `primeCharacter_at_int`, `primeGauss_scale_jacobi`, `primeGauss_sq_jacobi` | Identify the finite sum with a multiplicative Gauss sum, then obtain its scale and square in Jacobi-symbol form. |
| OrdinaryPhase.lean | `coe_action`, `theta_inversion`, `sqrt_mul_positive`, `ratio_odd_denom`, `ordinaryPhase_prime` | Normalize the inversion and root, compute the odd-denominator theta ratio, and compare the exact cube at a prime. |
| Assembly.lean | `changeLevel_unit`, `cusp_mul_half`, `evenUnaryStageLaw_of_ordinaryDilation`, `evenExpansion_of_ordinaryDilation` | Lift characters and bounds, assemble the original unary statement given the ordinary scalar, and transfer to weight two and the lattice. |
| Complete.lean | `theta_dilation_period`, `theta_dilation_ne`, `right_T_entries`, `ordinaryDilation_nontriangular`, `ordinaryDilationComparison_proved`, `evenUnaryStageLaw`, `evenExpansion_of_unary` | Use periodicity and right translation to finish the ordinary scalar and instantiate both exports with no remaining unary premise. |

## Verification

VERIFIED: all 13 proof modules passed direct `lake env lean` checks without `sorry`. The [scratch check](../../scratch/rc-even-unary/Audit.lean) prints the axiom closure of all 72 new theorems, including private helpers. [Its output](../../scratch/rc-even-unary/axioms.txt) contains only `propext`, `Classical.choice`, and `Quot.sound`. No existing statement or module was edited.

The direct checks used matching compiled imports from the base revision. A separate serial Lake dependency rebuild was started and stopped after the machine load crossed the prescribed limit. This did not leave any of the new modules or the axiom audit unchecked.
