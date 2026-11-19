**Result.** `GaussSign.oddGauss_one` proves
`oddGauss p 1 = (exponentRoot (oddBase (p.val : ZMod 4)) : ℂ)`
at every odd prime. The finite character in the manuscript is negative,
so the normalized value is 1 for p ≡ 1 (mod 4) and −i for p ≡ 3 (mod 4).
`gaussGamma_eq_finiteGamma` identifies the actual finite oscillatory
indices with the explicit eighth-root family. `gaussGamma_productFormula`
supplies the existing product-formula argument for every rational diagonal
list, and `gaussGamma_rectangular_products` exhibits the two rectangular
specializations with their common real factor. This discharges the scalar
Weil citation at tex 9000–9004 by proof. No print is added.

## Route and provenance

Route (iii), the cyclotomic congruence argument, fits Mathlib's minimal
polynomial for a primitive root, full cyclotomic product, finite field
power sums, and Wilson's theorem. The signed evaluation is standard
mathematics outside the manuscript's proof and its cited argument, so
the sign computation is on-the-spot (c). The inherited
`quadraticSum_eq_gaussSum` already identifies the sum over squares with
the quadratic-character Gauss sum; `oddGauss_sq` uses that identity to
compute the square. The inherited `oddGauss_twist` handles other units.

Write p = 2m + 1 and let ζ = exp(−2πi/p). Compare the sum over squares
with the product of ζ^a − ζ^(p−a) for a = 1, 3, …, 2m − 1. The
odd exponents and their complements partition the nonzero residues.
Squaring the product gives (−1)^m p by the full cyclotomic product for
ζ². In each factor the sine is positive for 2a < p and negative for
2a > p. There are ⌊m/2⌋ negative sines. The factor −i from each
difference, together with those signs, gives (−i)^(m mod 2) times
a positive real number; the square identifies that number as √p.

Use integral polynomials for the sum and product, translate X to X+1
and reduce modulo p. For the sum, multiplying the coefficient at
degree m by m! gives the sum of the monic polynomial
∏_{j<m}(x²−j) over the field; its degree is p−1, so the sum is −1.
For the product, the first coefficient of each factor after translation
is 2a modulo p and its constant term is zero. The product of these
coefficients times m! is (p−1)!, also −1 modulo p by Wilson.
If the two evaluations had opposite signs, their sum would vanish
at ζ and hence be divisible in ℤ[X] by the p-th cyclotomic polynomial.
After translation and reduction that divisor is X^(p−1), making the
degree-m coefficient of the sum zero. The computations instead give
−2 after scaling by m!, which is nonzero modulo the odd prime.

## Lean statements

All new theorems are in `ZInQ.Manuscript.RC.GaussSign`.
The table includes private lemmas. Throughout, p is prime and
p = 2m + 1 where that equation is used; `G` and `P` refer to
`squarePolynomial` and `oddProductPolynomial`.

| File | Theorem and statement | Input supplied |
|---|---|---|
| `Congruence.lean` | `sum_eval_monic`: a monic polynomial of degree p−1 sums to −1 on ZMod p. | Coefficient of G. |
| | `factorial_mul_choose_eq`: m! times the binomial coefficient ((x²).val choose m) is ∏_{j<m}(x²−j) in ZMod p. | Coefficient of G. |
| | `square_coeff`: the degree-m coefficient of G(X+1) times m! is −1 modulo p, for 2m = p−1. | Coefficient of G. |
| | `coeff_product_of_X_dvd`: the degree-n coefficient of a product of n polynomials divisible by X is the product of their degree-one coefficients. | Coefficient of P. |
| | `twice_odd_factorial`: n! ∏_{j<n} 2(2j+1) = (2n)!. | Coefficient of P. |
| | `product_coeff`: the degree-m coefficient of P(X+1) times m! is −1 modulo p. | Coefficient of P. |
| | `shifted_cyclotomic`: Φ_p(X+1) = X^(p−1) modulo p. | Divisibility after translation. |
| | `shifted_coeff_eq_zero`: if f ∈ ℤ[X] vanishes at a primitive p-th root, the degree-m coefficient of f(X+1) is zero modulo p for m < p−1. | Obstruction to the opposite sign. |
| | `eval_squarePolynomial_eq_of_sq`: equality of the squares of G(ζ) and P(ζ) at a primitive p-th root implies G(ζ) = P(ζ). | Resolves the sign ambiguity. |
| `Roots.lean` | `prod_odd_complement`: the product over pairs a,p−a with a odd equals the product over 1 through 2m. | Reindexes the full cyclotomic product. |
| | `eval_oddProduct_sq`: P(ζ)² = (−1)^m p for a primitive p-th root ζ. | Compares with `oddGauss_sq`. |
| | `negativeRoot_primitive`: exp(−2πi/p) is primitive for p ≠ 0. | Root for the manuscript character. |
| | `root_difference_sine`: at that root, ζ^a − ζ^(p−a) = −i·2 sin(2πa/p) for 0 < p and a ≤ p. | Phase of one factor. |
| | `sine_sign`: with a = 2j+1 and j < m, that sine is positive for j < (m+1)/2 and negative otherwise. | Sign of each sine. |
| | `prod_signs`: the product of those signs over j < m is (−1)^⌊m/2⌋. | Phase of the whole product. |
| | `eval_oddProduct_negativeRoot`: P(exp(−2πi/p)) = (−i)^(m mod 2) √p. | Signed value for the comparison. |
| `Sign.lean` | `negativeChar_eq_pow`: the inherited character at a is exp(−2πi/p)^a.val. | Identifies G with `quadraticSum p 1`. |
| | `exponentRoot_six`: the sixth power of the eighth root is −i. | Converts the phase to the existing exponent. |
| | `oddGauss_one`: `oddGauss p 1 = (exponentRoot (oddBase (p.val : ZMod 4)) : ℂ)` for p.val ≠ 2. | The previously missing odd-prime phase at unit 1. |
| `Product.lean` | `unit_sign_root`: the eighth root at the sign exponent of the quadratic character of a unit equals that character. | Incorporates the inherited unit twist. |
| | `gaussGamma_eq_finiteGamma`: `gaussGamma = finiteGamma`. | Identifies the actual finite family. |
| | `gaussGamma_productFormula`: `WeilIndexProductFormula gaussGamma`. | Both support and product-one clauses of the existing argument `hγ` to `pair_of_tensor_generators`. |
| | `gaussGamma_rectangular_products`: the real index of `rationalDiagonal a` times the actual finite product is 1 on each of `rationalDiagonal a` and `rationalDiagonal referenceForm`. | The two product-one identities used in the comparison. |

No new structure or named Prop is introduced. At the use of
`eval_squarePolynomial_eq_of_sq`, the square equality follows from the
inherited local square calculation and the cyclotomic product for tex
8746–8753. It is strictly weaker than the equality of evaluations,
since squaring identifies both signs; the coefficient
comparison is a separate proof. Primitivity, primality, parity and the
ranges of indices are domain conditions for this same evaluation. The
monicity and degree, divisibility by X, and vanishing-at-the-root
hypotheses describe auxiliary polynomials. They determine neither the
sign of the Gauss sum nor a Weil product, and they are discharged where
used. The existing nonzero hypotheses on the rectangular coefficients
supply nondegeneracy for tex 9000–9004.

All four files pass sequential `lake env lean`. Every new theorem has
a `#print axioms` check; all 23 checks report only `propext`,
`Classical.choice`, and `Quot.sound`.

## Remaining hypotheses

There is no remaining hypothesis for the actual finite Weil index
product formula. The other hypotheses of the base report are unchanged:

1. **Common lifts and actions — metaplectic sibling lane.** Tex
   8726–8807, 8990–9004. Supply both `GeneratorTensorAction` instances
   on the actual common inverse lifts (for a and `referenceForm`),
   their common central kernel for the stage quotient, and the
   realization and lift compatibility required by
   `pair_of_tensor_generators`. The scalar product argument is now
   supplied; it does not construct these actions.
2. **Old-level realization — stage and local weight sibling lanes;
   ELLIOT input for the exact level.** Tex 8499–8596, 8654–8685,
   8837–8886, 8925–8936, 9030–9036, 9471–9479. Supply the conductor
   characters and unit-scaling laws of the prescribed weights, their
   sign at −1 where used, and the classwise depth and spherical inputs
   for the fixed-sieved weight at `Dₗ.old`. The precise additional
   level data for the residue construction are m ∣ `Dₗ.old` and
   c_p ∣ `Dₗ.old` for the conductor levels c_p; four-divisibility is
   already available. `StageGrid` and the resulting
   `RelativeFiniteAction` remain inputs of `oldStageLaw_of_finiteAction`.
3. **Fixed-pool identification — ELLIOT input.** Tex 8891–8936,
   8978–8986, 9012–9015. At computational level M, for every signed
   residue unit u with canonical representative d, the complex image
   of `bCharacter(C, ∅)(u)` must equal
   (∏_p α_p(u mod c_p)) Jacobi(m,d). The inherited
   `oldCharacter_comp_eq_iff` turns this test at `Dₗ.old_dvd` into
   the precise `hchar`.

The optional norm-form cross-check at tex 8696–8716 would require the
local theory identifying the symbol from the quaternion norm with
the explicit local factors. It is not a hypothesis of the product.

## Known issues

- No manuscript or source error was identified within scope. The
  positive additive character gives +i for p ≡ 3 (mod 4); the finite
  character at tex 8641 and in `oddGauss` gives −i.
- Weil I.14, Theorem 2 and II.30, Proposition 5 are the manuscript's
  locators, independently **UNVERIFIED**. No page number or source
  wording is claimed. The sign proof does not invoke either citation.

## Manuscript check

- Tex 8640–8642 — **OK**: the finite character has negative argument; the proof uses its reduction at an odd prime.
- Tex 8643–8653 — **OK**: the polar Haar normalizations are inherited in the actual finite indices and real Gaussian calculation.
- Tex 8694–8695 — **OK**: orthogonal multiplication on diagonal lists is inherited as `gammaDiag`.
- Tex 8731–8738 — **OK**: the normalizing factors use the actual local indices, and the index of a rescaled form is covered by the same rational-list product.
- Tex 8746–8753 — **gap filled**: the inherited oscillatory evaluation identifies the finite local sum, and this proof fixes its remaining odd-prime sign.
- Tex 9000–9004 — **gap filled**: the scalar product-one identities follow for the actual family from the signed evaluation and scalar reciprocity. The compatibility of the lifts is a separate input.
- Tex 9009–9011 — **OK**: both positive ternary lists have the same real index by the inherited real factor. The rotation action is outside this scalar proof.
