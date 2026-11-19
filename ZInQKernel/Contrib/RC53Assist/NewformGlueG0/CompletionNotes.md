# G0 completion: exact consequences and source boundaries

## Status and the two retained routes

The unchanged target is
`ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular`.
The contribution gives two conditional assemblies of that target, not
unconditional proofs of the literature inputs:

1. `Descent.liCarayolNewformOfModular_of_printed_corollaries` in
   `GaloisCompletion.lean`, with its four original input propositions and
   supporting code unchanged. The two local-factor interfaces are GLUE;
   Shimura's conjugate-eigenform and Li's strong-multiplicity-one interfaces
   remain PRINT specializations.
2. `GlobalTrace.liCarayolNewformOfModular_of_representations_coinv` in
   `GlobalTrace/CoinvariantAssembly.lean`, using the corrected coinvariant
   realization, the proved global good-prime reading and the displayed
   bad-prime reading. Its `_of_inputs` version replaces the bad-prime reading
   by the Tate-curve, local–global and additive-vanishing inputs.

The earlier invariant-space representation route is removed from the Lean
source. Its declarations and the multiplicative-reduction obstruction are
preserved as historical text in
`docs/research/g0-representation-route-invariants.md`. It must not be read
as another active route or as a collection of valid local-factor inputs.

All displayed literature and arithmetic inputs are propositions used as
theorem parameters, not new axioms. No input asserts the newform-existence
conclusion for the original elliptic curve.

## The protected coefficient-field descent

For a genuine weight-two trivial-character newform `F`,
`Descent.coefficientField F` is the actual subfield
`ℚ(a_n(F) : n ≥ 0) ⊆ ℂ`.

`Shimura1973ConjugateEigenforms` keeps the finite coefficient-field and
conjugate-eigenform reading of Shimura 1973, Theorem 1, p. 526, with its
setting and definitions on p. 525. `Li1975StrongMultiplicityOneWeightTwo`
keeps the weight-two trivial-character specialization of Li 1975,
Theorem 5, p. 298. Their complete source quotations are in the corresponding PRINT docstrings;
the Lean proposition bodies are unchanged.

The existing proofs retain every step:

* A coefficient-field embedding fixes the elliptic curve's integer prime
  coefficients outside the given finite set.
* The old/new decomposition extracts a divisor-level newform from the
  conjugate full eigenform, preserving the trivial character.
* Li's strong multiplicity one identifies the level and the newform.
* Whole-character-space multiplicity one identifies the full conjugate form
  at every coefficient.
* Equality of all coefficient-field embeddings gives degree one over `ℚ`,
  and the rank-one argument proves every coefficient rational.

These are `fullEigenform_divisor_newform`, `embedding_fixes_coefficients`,
`coefficients_rational_of_almost_all_primes` and
`coefficientField_eq_bot_of_almost_all_primes`. Their code is unchanged.

## Local-factor labels on the printed-corollary route

`Carayol1986RationalNewformEulerFactors` is **GLUE**: joint reading of
Shimura 1973, Thm 1, and Carayol 1986, §0.8 Corollaire; GLUE until a two-lens
skeptic pass clears it. Its associated-curve and Weierstrass local-polynomial
readings are not presented as a verbatim printed implication.

`Faltings1983EulerFactorRigidityQ` is **GLUE**: local-factor reading of
Faltings 1983, §5, Korollar 2 (iii ⇒ iv); GLUE unless restated as the printed
implication with the local-factor step proved.

The proof starts with the extracted newform and proves its rationality,
then uses the associated elliptic curve `A` supplied by the joint reading.
It does not assert `A = E`. Agreement of prime coefficients almost everywhere
is converted by the proved arithmetic dictionary into agreement of local
polynomials almost everywhere. The Faltings reading supplies equality at
every finite place. The prime-power recurrence and coprime multiplicativity
then give all positive Fourier coefficients, at exactly the original level
and quantifier order.

`Descent.newformOfModularCurveGlue_of_printed_corollaries` returns the
original newform-periods interface through the existing subgroup and
full-eigenform conversion. Both assemblies, the four input proposition
bodies and their supporting code are preserved without code changes.

## Actual Tate representations and the good-prime proofs

`Completion.integralTateRep E ℓ` is the coordinatewise Galois action on
`T_ℓ(E(AlgebraicClosure ℚ))`. `rationalTateRep E ℓ` is its scalar extension
to `ℚ_ℓ`, and `extendedTateRep E ℓ K` is the further extension to a common
field. The displayed bases, dimensions and continuity proofs are preserved.

`LocalArithmeticFrobenius` contains an actual valuation place, a Galois
element, the arithmetic residue action and the integral-closure Frobenius
reading. Its existence at every rational prime is proved. `inertiaAt` is
the actual inertia kernel mapped from the decomposition group; normalization
by Frobenius is proved in both conjugation directions used by the two
local-polynomial definitions.

`Completion.goodReductionFrobeniusTraceDictionaryQ_proved` retains the
existing local trace-and-determinant dictionary. In
`GlobalTrace/GoodReductionReading.lean`, the rational-model construction,
place-reduction homomorphism, torsion bijectivity, inertia triviality and
Tate-module trace and determinant proofs all remain.
`globalGoodReductionTraceReading_proved` proves the global reading directly
at a place of the algebraic closure of `ℚ`; its local-dictionary premise is
not needed. Faltings 1983, §5, Satz 3, p. 360, remains the explicit rational
Tate semisimplicity proposition.

`Completion.localTatePolynomial` is retained as the literal invariant
polynomial with its warning. At multiplicative reduction it is
`1 − εpX`, not the classical `1 − εX`; for 11a1 at `p = 11`, these are
`1 − 11X` and `1 − X`. Its good-prime equality with the classical polynomial
is true and remains proved.

## The corrected coinvariant route

The local readings and representation assembly are in
`GlobalTrace/CoinvariantReadings.lean` itself. `CarayolRationalRealizationCoinv`
retains the original types of `normalizedRep`, `continuous_matrix`,
`irreducible` and `good_trace`; only the local-factor reading uses inertia
coinvariants. The true dual-normalization definition is now
`CarayolRationalRealizationCoinv.cohomologicalRep`.

`tate_equiv_of_good_traces` uses the proved characteristic-zero
Čebotarev–Brauer–Nesbitt comparison and only the good-prime representation
properties. `localTatePolynomialCoinv_eq_newform_of_comparison` transports
the corrected polynomial through that isomorphism. All existing coinvariant
linear-algebra, local comparison, additive- and multiplicative-reduction
proofs are preserved.

`coinvariantEulerPolynomial_eq_dual` and the two local corollaries identify
arithmetic Frobenius on the homological coinvariants with geometric
Frobenius on the cohomological inertia invariants. The assembly always
chooses `ℓ ≠ p`, so it never uses a local-compatibility clause at its excluded
auxiliary prime.

The corrected bad-prime reading is conditional on its stated inputs:
`TateCurveTateModulePrint`, `DecompositionGroupLocalGlobalGlue` and
`AdditiveReductionCoinvariantsVanish`. The first includes derived Tate-module
readings; the latter two are GLUE. They are not newly proved here.

## Literature locators and historical records

* Shimura 1973, *On the factors of the jacobian variety of a modular function
  field*, J. Math. Soc. Japan 25, 523–544: Theorem 1, p. 526, definitions p. 525.
* Li 1975, *Newforms and Functional Equations*, Math. Ann. 212, 285–315:
  §2 p. 294; Theorem 3(i), (iii), p. 295; Theorem 5, p. 298.
* Carayol 1986, §§0.4–0.6 pp. 409–410; Théorème (A), §0.7 pp. 410–411;
  irreducibility Remarque and rational Corollaire, §0.8 p. 411.
* Casselman 1973, Theorem 1 and proof pp. 302–306; Corollary p. 306;
  ε-factor Remark p. 307; Theorem 4, p. 313.
* Faltings 1983, §5, Satz 3 p. 360; Korollar 2, iii ⇒ iv, p. 361.
* Silverman, *The Arithmetic of Elliptic Curves*, III.7, VII.3–VII.7,
  Appendix C, §14 and §16.

`Scratch/CompletionTheoremStatements.md` and `Scratch/TheoremStatements.md`
are historical records of the earlier editions. They are not verification
claims for the current declaration inventory. The excluded statements are
not edited back into the source merely because those historical records
contain their former types.
