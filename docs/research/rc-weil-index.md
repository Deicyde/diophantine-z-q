**Result and scoped stop.** `finiteGamma_productFormula` proves the exact
`Intertwine2.WeilIndexProductFormula` predicate for the explicit finite
eighth-root family `finiteGamma`, for every list of nonzero rational
coefficients. In particular it supplies the product argument `hγ` of
`pair_of_tensor_generators` for `a` and `referenceForm` with
`γ := finiteGamma`. The proof is direct from quadratic reciprocity and
the supplements for −1 and 2. Separately, `gaussGamma` constructs
the actual finite indices: it is proved to give the normalized shifted
oscillatory integral for every finite place and nonzero coefficient.
The real Gaussian limit gives the inherited `gammaReal`. The actual
finite factors are one outside finitely many primes. The outstanding
product step is the signed value of the ordinary Gauss sum at unit 1:
it would identify the actual family with `finiteGamma`. The character
calculation gives the odd and dyadic defects of the actual indices,
descends the character to signed residues at the supplied old level,
and reduces the fixed-pool identification to its exact pointwise test.
The old-level conductor bounds and that fixed-pool test have not been
supplied.

Write $a=p^v u$, with $v\in\mathbb Z$ and $u\in\mathbb Z_p^\times$.
With the manuscript's negative finite additive character and
$\zeta_8=\exp(2\pi i/8)$, the explicit phase is:

| Place | Case | Factor |
|---|---|---|
| $p\ne2$ | $v$ even | $1$ |
| $p\ne2$ | $v$ odd | $\left(\frac{u}{p}\right)$ times $1$ for $p\equiv1\pmod4$, and times $-i$ for $p\equiv3\pmod4$ |
| $2$ | $v$ even | $\zeta_8^{-\chi_4(u)}$ |
| $2$ | $v$ odd | $\zeta_8^{-u}$, with $u$ read modulo eight |
| Real | $a>0$ or $a<0$ | $\zeta_8$ or $\zeta_8^{-1}$, respectively |

These are the standard one-dimensional quadratic Gauss computations:
the odd-prime normalized quadratic Gauss sum and its Legendre twist, the
dyadic sums modulo four and eight, and the real Fresnel integral. The
explicit arithmetic model, direct product argument, finite residue
computations and Gaussian damping are on-the-spot (c). The sign at an odd
prime in the table is the classical signed evaluation; the Lean proof
currently evaluates its square and its twist, not the sign. The dyadic
residue sums are evaluated with their signs. The measure for a line is
$dx_a=\sqrt{\lvert2a\rvert_p}\,dx$, with $\operatorname{vol}(\mathbb Z_p,dx)=1$,
and $dx_a=\sqrt{\lvert2a\rvert_\infty}\,dx$ at infinity. The quotient phase is
literally the restriction of the local Fourier character. Orthogonal
multiplication is the existing `gammaDiag`; the real factor of each
positive ternary form is the existing $\zeta_8^3$.

For the product proof, a rational square reduces the coefficient to
$\sigma 2^e M$, where $M$ is a product of distinct odd primes,
$\sigma=\pm1$, and $e\in\{0,1\}$. An odd prime outside $M$ gives one.
For the remaining odd primes, quadratic reciprocity pairs the cross
terms $(p/q)(q/p)$; its sign combines with the local fourth roots to
give `oddBase` of $M\bmod4$. The supplements replace the terms from
$\sigma$ and $2^e$ by the characters of $M\bmod4$ and $M\bmod8$.
The resulting exponent, plus the dyadic and real exponents, is zero in
$\mathbb Z/8$. The proof then reinstates the rational square and
multiplies over the list. It also applies to rational rescalings of the
two lists.

For the old character, the quotient of four line indices has the odd
unit value $\left(\frac{d}{p}\right)^{v_p(m)}$ and the dyadic unit
value $(-1)^{((d-1)/2)((m-1)/2)}$. These are the explicit Hilbert
symbol values in the manuscript. At odd primes the base Gauss sign
cancels from the quotient, so the calculation works directly for the
actual indices. At two the explicit and integral definitions agree.
There is no independent comparison to a norm-form definition of the
Hilbert symbol. For $m\equiv3\pmod4$, the
determinant factor on signed units is $\chi_4(d)\operatorname{Jacobi}(d,m)$.
It is even and equals $(m/d)$ on positive representatives by quadratic
reciprocity. The existing `Odd.psi_div_eta` is the Jacobi quotient with
the genus character. Given the characters $\alpha_p$ on their conductor
quotients, `oldCharacter` multiplies their pullbacks by the determinant
factor. This gives $\xi(d)=\prod_p\alpha_p(d)(m/d)$; the inverse lift
in the manuscript places $d$ in this formula.

## Lean statements and consumers

All names below are in `ZInQ.Manuscript.RC.WeilIndex`.

| File | Theorems and statements | Input supplied |
|---|---|---|
| `Reciprocity.lean` | `signExponent_mul`: multiplication of signs adds exponents; `jacobi_sign`: a coprime Jacobi symbol is ±1; `qrSign_cases`: reciprocity sign for two odds; `oddBase_mul`: the mod-four exponents add up to that sign; `odd_prod`, `prime_coprime_prod`: oddness of an odd product and coprimality with an omitted prime; `jacobiExponent_prod`: exponents distribute over the Jacobi factors. `odd_squarefree_exponents`: sum of the cross terms and the local base exponents equals `oddBase` of the product. `odd_coprime_two`, `signed_odd_squarefree_exponents`: add the two supplements for the signed product. `total_exponent`: real, dyadic and odd exponents add to zero on odd residues modulo eight. | Arithmetic input to `hγ`. |
| `Local.lean` | `eighth_pow`, `exponentRoot_add`, `exponentRoot_neg`: the root has eighth power one and exponents multiply and invert correctly. `exponentRoot_zero`, `exponentRoot_one`: zero gives the unit and one gives the chosen eighth root. `place_cast_ne_zero`, `unitField_norm`, `unitInteger_isUnit`, `unitAt_coe`: the uniformizer is nonzero and dividing out the valuation produces a unit of norm one with the stated field value. `valAt_mul`, `unitAt_mul`, `oddUnitResidue_mul`, `dyadicUnitResidue_mul`: valuations add and unit parts and residues multiply. `finiteExponent_dyadic`, `finiteExponent_odd`, `finiteGamma_even_odd_place`: the formula branches and value one at even valuation away from two. `zmod8_unit_sq`, `finiteExponent_mul_sq`, `finiteGamma_mul_sq`: invariance under a square. `unitAt_of_int_times_pow`: for a coefficient given as a prime power times a prime-to-$p$ integer, its valuation is the power and its unit part is the integer. | Defines the candidate `γ` for both consumers. |
| `Product.lean` | `signedCoefficient_ne_zero`, `atPrime_rationalUnit`, `atReal_rationalUnit`: the signed squarefree coefficient is nonzero and maps to the same scalar. `not_dvd_signedCoefficient`, `dyadic_signed`, `odd_signed`, `odd_outside`, `atReal_signed`: local values on the representative and prime support contained in its odd prime factors together with two. `exponentRoot_sum`, `signed_product`: exponent sum becomes product one. `rational_squarefree`, `gammaReal_sq`: existence of the squarefree representative and real square invariance. `rational_weil_product`: finite support and product one for one rational unit; `finiteGamma_productFormula`: both clauses for any list of rational units. | Supplies the literal `hγ` of `pair_of_tensor_generators`. |
| `Gauss.lean` | `localPhase_fraction`: $j/p^n$ has the finite negative residue phase. `shifted_negative_primitive`, `quadraticSum_eq_gaussSum`: a unit twist is primitive and the odd sum over squares equals the quadratic-character Gauss sum. `oddGauss_sq`, `oddGauss_twist`: the normalized odd sum squares to the sign of −1, and is determined by the value at the unit 1 and its Legendre twist. `quadraticSum_four`, `stdChar_eight`, `quadraticSum_eight`: the mod-four sum is $2(1+\mathbf e_4(u))$, the mod-eight standard phase is the corresponding power of $\zeta_8$, and the mod-eight sum at a unit is $4\zeta_8^{-u}$. `negativeFour`, `eighth_add_inv`, `eighth_normalized`: the mod-four negative phase and square-root-of-two normalization. `dyadic_evenGauss`, `dyadic_oddGauss`: the two sums divided by $2\sqrt2$ and $4$, respectively, yield the explicit dyadic phases. | Partial finite analytic identification for `GeneratorTensorAction`. |
| `Integral.lean` | `lineHaar_integerBall`: polar Haar mass of the integer ball; `integral_completeSquare`: shift by a vector of the cutoff lattice gives exactly the stationary phase. `localPhase_congr_integer`, `localPhase_integer_div_pow`: congruence modulo integers and the precise quotient phase of an integral numerator. `odd_unit_integral`: the integral on the integer ball is the explicit phase for odd $p$ and valuation zero. `integral_linearPhase`, `integral_quadratic_coset`: character orthogonality on the subgroup and the corresponding coset formula, zero off the polar dual. `cutoffLattice_measurable`, `eventually_cutoffLattice`, `eventually_cutoffGaussian`: large cutoffs are measurable, contain any fixed shift eventually, and satisfy completion of the square. `continuous_localPhase`, `norm_localPhase`: the local character is continuous with modulus one. `polarDualLattice_measurable`, `integral_quadratic_polarDual`: the dual is measurable and averaging restricts the integral to the dual. `scaledLattice_compact`, `eventually_scaledLattice_subset`, `polarDualLattice_scaled`: nonzero scaled lattices are compact, eventually lie in the cutoff and have the expected polar dual. `eventually_cutoffGaussian_polarDual`, `eventually_cutoffGaussian_at_valuation`: the zero-shift integral stabilizes on a fixed polar dual; the valuation gives an eligible lattice for each nonzero coefficient. `eventually_odd_unit_integral`: the shifted integral equals the explicit phase at an odd prime and unit coefficient. | Analytic input to the finite normalization. |
| `ResidueHaar.lean` | `residueFiber_eq`, `iUnion_residueFiber`, `residueFiber_disjoint`: the residue fibers are translates of the same lattice and partition the scaled lattice. `integral_scaledLattice_residue`, `lineHaar_scaledLattice_div`, `scaledLattice_one`, `lineHaar_scaledLattice_zpow`, `scaledLattice_eq_of_valuation`: sum with the common Haar mass, its ratio and its value for uniformizer powers, and equality of scaled lattices of equal valuation. `eventually_cutoffGaussian_eq_quadraticSum`: the stabilized integral is the normalized sum at depth $e+2v_p(2)$. `quadraticSum_cast`, `toZModPow_one`, `depth_two_odd`: compatibility of casts, reduction at depth one, and the valuation of two away from two. `eventually_odd_evenGauss`, `eventually_odd_oddGauss`, `eventually_dyadic_Gauss`: stabilized values of one, the normalized ordinary sum, and the explicit dyadic phases in the respective cases. `eventually_cutoffGaussian_gaussGamma`: the actual family gives the normalized shifted integral. | Supplies the scalar normalization needed by `GeneratorTensorAction`; not the actions or lifts. |
| `Actual.lean` | `gaussGamma_of_even`: actual coefficient value one for even valuation at an odd prime. `gaussGamma_rational_finite`, `gaussGamma_indexAt_finite`: finiteness for rational scalars and diagonal lists. `gaussGamma_odd_unit_defect`, `gaussGamma_dyadic_unit_defect`: the odd Legendre and dyadic mod-four factors for the actual indices. | Supplies the finiteness half of the actual product condition and the actual character factors. |
| `Real.lean` | `zetaEight_sq_complex`, `zetaEight_re`: square $i$, positive real part for either index. `gaussianParameter_re`, `gaussianParameter_zero`, `pi_div_parameter`: damping parameter and its boundary value, with quotient $i/(2a)$. `real_gamma_sq`, `pi_div_parameter_sqrt`: the square is the signed imaginary unit and the principal square root with the Haar factor is `gammaReal`. `real_normalized_gauss_limit`: the resulting damped integrals converge to `gammaReal` as damping tends to zero from above. | Identifies the real scalar used by `pair_of_tensor_generators`. |
| `Determinant.lean` | `determinantExponent_value`: the exponent gives the exact four-index quotient. `odd_unit_determinantExponent`: at odd $p$ this quotient is trivial for even coefficient valuation and otherwise the unit Legendre sign. `zmod8_chi4_sign`, `dyadic_unit_exponent_mul`: mod-eight unit arithmetic; `dyadic_unit_determinantExponent`: the exponent at two for two units is 4 exactly when both are 3 modulo 4. | Supplies local numerical factors in the character row. |
| `Character.lean` | `jacobi_congr`, `jacobiOn_intCast`, `jacobiOn_unit`, `unitsMap_intCast`: Jacobi symbols descend modulo the denominator, are signs on units, and are compatible with reduction of signed representatives. `determinantCharacter_intCast`: signed formula above; `determinant_reciprocity`, `determinantCharacter_natCast`: positive formula by reciprocity; `determinantCharacter_neg_one`: evenness. `jacobi_prod_right`, `oddFactors_eq_jacobi`: multiply the local prime factors with the correct valuations; `dyadic_sign`: the signed dyadic formula. `oldCharacter_natCast`: evaluation of the full character on positive residues. `oldCharacter_comp_eq_iff`: equality of the pullback with any computational character is equivalent to the displayed formula on canonical positive unit residues there. | Constructs `ξ` once the conductor bounds are given, and gives precisely the test for `hchar` of `oldStageLaw_of_finiteAction`. |

There are no new structures or named Prop inputs. The measurable
subgroup, inclusion of the stationary shift, and trivial-quadratic-phase
conditions in `Integral.lean` are local domain conditions for a
change of variables or cancellation (tex 8646–8662, 8746–8753); they
give no value for the stabilized integral. Compactness, inclusion and
positive mass for the averaging lattice are geometric domain
conditions in the same manuscript step. The residue-factoring
condition in `integral_scaledLattice_residue` only specifies the
integrand; it does not assign any mass or integral to it. Divisibility and the
conductor homomorphisms in `Character.lean` concern only the source
of the reduction maps (tex 8897–8901, 8925–8936). In particular they
make no claim about the unrelated fixed-pool character.

## Finite integral calculation

The one-dimensional normalization from tex 8640–8650 and
8746–8753 is proved for every finite place. Write $e=v\bmod2$ and
$\delta=v_p(2)$, and let $G_n(u)$ be the negative quadratic sum
modulo $n$. The value at zero shift is
$$
  \frac{G_{p^{e+2\delta}}(u)}{p^{(e+3\delta)/2}}.
$$
The cancellation argument uses $H=p^k\mathbb Z_p$ with
$k=(e-v)/2$. Its polar dual is $p^s\mathbb Z_p$ with
$s=-v-\delta-k$. Averaging over $H$ removes the region outside the
dual. On the dual, $x=p^s z$ gives exponent
$a x^2=u z^2/p^{e+2\delta}$ and normalized mass $p^{(e+\delta)/2}$;
residue fibers have equal mass. For tex 8751 replace $a$ by $ba$ and
the shift by $v/b$, and account for the change of Haar by
$\lvert b\rvert_p^{-1/2}$ per line. Tensoring the scalar identities
gives the exponent $-3/2$ of the manuscript.

## Remaining hypotheses

1. **Signed ordinary Gauss sum — missing theory, a separate classical
   signed evaluation.** Tex 8731–8738, 8746–8753, 9000–9004. The
   smallest remaining finite algebraic result is
   `oddGauss p 1 = (exponentRoot (oddBase (p.val : ZMod 4)) : ℂ)`
   for $p\ne2$. Mathlib's `gaussSum_sq` gives the square; the twist is
   already proved. This identity would give `gaussGamma = finiteGamma`
   and hence the product-one clause for the actual family. Choosing
   either square root would not identify the actual product. A signed
   evaluation, for example via a cyclotomic congruence or a computation
   of the sign of the finite Fourier determinant, requires an
   independent Gauss-sum argument beyond the implemented residue/Haar
   theory.
2. **Common lifts and actions — metaplectic sibling lane.** Tex
   8726–8807, 8990–9004. Both instances of `GeneratorTensorAction` on
   the actual common inverse lifts, for $a$ and `referenceForm`, and
   their common central kernel for the stage quotient. The conditions
   on the realization maps and lifts in `pair_of_tensor_generators`
   remain the existing interface. The quaternion norm-form argument
   at tex 8696–8716 was not used; an independent cross-check against a
   norm-form Hilbert symbol would require that symbol's local theory.
3. **Old-level realization — stage and local weight lanes; ELLIOT
   input for the exact level.** Tex 8499–8596, 8654–8685, 8837–8886,
   8925–8936, 9030–9036, 9471–9479. Supply the conductor characters of
   the prescribed weights, their unit-scaling laws and sign at $-1$
   as needed, and the classwise depth and spherical inputs for the
   fixed-sieved weight at `Dₗ.old`. For the present residue construction
   the required level data are $m\mid D_\ell.\mathrm{old}$ and $c_p\mid D_\ell.\mathrm{old}$;
   $4\mid D_\ell.\mathrm{old}$ is already `Dₗ.four_dvd`. There is no enlargement
   of `Dₗ.old`. `StageGrid` and the resulting `RelativeFiniteAction`
   for its weight are still arguments of `oldStageLaw_of_finiteAction`.
4. **Fixed-pool identification — ELLIOT input.** Tex 8891–8936,
   8978–8986, 9012–9015. Let $M$ be the supplied computational level
   and $d=(u:\mathbb Z/M).\mathrm{val}$ for
   $u\in(\mathbb Z/M)^\times$. The remaining proposition is
   $$
   ((\mathrm{Units.map}\,\kappa)\circ \mathrm{bCharacter}(C,\varnothing))(u)
     = \left(\prod_p \alpha_p(u\bmod c_p)\right)\operatorname{Jacobi}(m,d),
   $$
   as complex values. Use `oldCharacter_comp_eq_iff` with
   `Dₗ.old_dvd`; it turns this proposition into the exact `hchar`,
   independently of the analytic action and of the weights of
   `StageGrid`.

## Known issues

- No manuscript error was identified in scope. The odd Gauss sign is an
  outstanding formal proof, not an ambiguity in the manuscript's
  convention. Using the positive local additive character in its place
  would change the finite phases.
- The preexisting old-level setup gives divisibility by four and the
  relation to the computational level. It does not record the
  conductor bounds for the manuscript's weights.
- Weil II.30, Proposition 5 is the manuscript's locator and is
  independently **UNVERIFIED**. The same applies to its locators
  I.14, Theorem 2; II.25; II.28, Proposition 4; and III.41,
  Theorem 6. No source wording, pagination, or independent source check
  is claimed. No print was added: the direct scalar reciprocity proof
  succeeds for the explicit eighth-root family. A print of the product
  formula would bypass the requested signed Gauss evaluation rather
  than prove it from the local calculation.

## Manuscript check

- Tex 8640–8642 — **gap filled**: the exact finite quotient character, with the negative sign; the additive adèlic product is not reproved.
- Tex 8643–8653 — **gap filled**: polar scalar Haar and its real Gaussian limit; the general inversion statement is not used.
- Tex 8654–8662 — **gap filled**: cancellation on a subgroup off its polar dual, in the scalar case.
- Tex 8677–8685 — **unverified**: stage depth and reference-vector invariance are outside this calculation.
- Tex 8688–8695 — **gap filled**: the four-factor quotient is computed directly on the relevant unit arguments for the actual indices.
- Tex 8696–8724 — **unverified**: the quaternion norm-form proof is not needed for the direct numerical calculation.
- Tex 8726–8744 — **OK**: the index enters the inherited Weyl normalization as the scalar multiplying the positive-sign polar Fourier transform for the specified character.
- Tex 8746–8753 — **gap filled**: the stationary phase and real normalization are formalized; the finite Haar integral reduces to the normalized residue sum, and both dyadic parities have their exact phases.
- Tex 8746–8753 — **unverified**: the finite scalar is identified with the normalized sum; its signed odd Gauss evaluation at unit 1 remains.
- Tex 8754–8807 — **unverified**: the common cover and relations belong to the metaplectic lane.
- Tex 8888–8901 — **gap filled**: square invariance and unit defects give the odd valuation factor and the dyadic mod-four factor.
- Tex 8903–8919 — **gap filled**: quadratic reciprocity gives the Jacobi factor and its even extension; the genus quotient is already in the shared odd layer.
- Tex 8925–8936 — **gap filled**: evaluation at $d$ and descent through the supplied conductor maps are expressed on signed unit residues.
- Tex 8925–8936 — **unverified**: the comparisons of actual conductors and weight signs at the supplied old level remain.
- Tex 8978–8986 — **gap filled**: arithmetic of the extracted relative character; its realization on the prescribed vector remains separate.
- Tex 8990–8999 — **unverified**: the identity of realized lifts is outside this calculation.
- Tex 9000–9004 — **gap filled**: direct product one for the explicit family and actual finiteness for every rational diagonal list; the signed Gauss evaluation is still needed to identify the two products.
- Tex 9005–9008 — **unverified**: rational invariance is not invoked; the Haar normalization is inherited from the restricted-product comparison.
- Tex 9009–9011 — **gap filled**: the normalized real scalar agrees with the existing index; no new rotation or weight law is needed here.
- Tex 9012–9015 — **gap filled**: the exact canonical residue test for the old character identification.
- Tex 9030–9036, 9471–9479 — **unverified**: the actual fixed-sieved vectors and their support and stabilizer conditions are outside this calculation.
