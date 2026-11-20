# Newform period reading dictionaries

This collection preserves the original conditional package, its propositions, and its targets. The namespace is `ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary`.

## Proved translations

- **S4: the Weierstrass coefficient and Euler-polynomial dictionary.** For a rational prime `p` of good reduction, `lFunction_prime_eq_card_ZMod` proves that the genuine global coefficient `E.LFunction p` is `p + 1` minus the number of points of the actual minimal reduction over `ZMod p`. The point at infinity is included. Ellipticity and finiteness of the counted reduction are proved.
- The coefficient proof passes through the global Euler product, the completed residue field, its prime-ideal norm, injectivity of the rational prime-ideal norm, and the linear coefficient of the local reciprocal power series. It is not a replacement definition of `LFunction`.
- **F1: the arithmetic portion.** Almost-all prime-coefficient agreement is equivalent to almost-all agreement of the existing local polynomials. Good reduction outside a finite set is proved, not assumed. The local reciprocal series, local arithmetic factors, and evaluations at `p^{-s}` then agree almost everywhere, including on the genuine rational finite-place type. The analytic evaluation is exactly `(1 - a_p p^{-s} + p^{1-2s})^{-1}` at good primes.
- **S5: the weight-two Hecke normalization.** The existing full Hecke-ring action is transported to the actual cusp-form space on `Gamma0 M`. Its divisor-sum coefficient formula holds at every positive index, including the bad indices. At `p` prime to `M`, it gives `a_m(T_p g) = a_{mp}(g) + p a_{m/p}(g)`, where the last coefficient is zero if `p` does not divide `m`. The normalization determines the operator on actual cusp forms. The original normalized-full-eigenform predicate is equivalent to the normalized common-eigenfunction predicate in this normalization.
- **F2: the function-field portion.** A pointed embedding of the actual Weierstrass function fields gives a genuine `TauCeti.Isogeny`, and conversely. Pointedness means that restricting the source infinity valuation gives a valuation equivalent to target infinity. The constructed isogeny induces exactly the supplied field map.

## Explicit remaining Frobenius proposition

`GoodReductionFrobeniusTraceDictionaryQ` is defined as a proposition and is **not proved**. It states that, at good reduction and for every auxiliary prime different from `p`, arithmetic Frobenius on the actual local elliptic-curve Tate module has trace `p + 1 - #E(F_p)` and determinant `p`, in every basis. Its valuation-extension and arithmetic-Frobenius congruence hypotheses are explicit. The Tate-module basis is proved to exist.

Sources: Silverman, *The Arithmetic of Elliptic Curves*, second edition, V.2 and VII.7: the finite-field Frobenius polynomial and good-reduction Tate specialization.

`tateEulerPolynomialQ_eq_localPolynomial_of_dictionary` proves the exact determinant-versus-local-polynomial comparison from this proposition. `tateEulerPolynomials_equal_almost_all_primes` proves almost-all agreement of the genuine Frobenius determinant polynomials from coefficient agreement and the same explicit proposition. Neither theorem assumes a printed leaf or the period conclusion.

## Reformulated printed interfaces

- `Shimura1973EulerPolynomialFormQ` uses the normalized common-eigenfunction predicate and explicit good-prime Euler polynomials. Its exceptional set also contains the primes of the level.
- `Faltings1983LocalPolynomialFormQ` uses cofinite local-polynomial agreement and a pointed function-field embedding.
- `shimura_eulerPolynomialForm_iff` and `faltings_localPolynomialForm_iff` prove that these specialized consequence forms have exactly the same conditional content as the original two interfaces.
- `someLevelPeriodsRational_of_dictionaryLeaves`, `newformPeriodsRational_of_dictionaryLeaves`, and `modularToWeakWeil_of_dictionaryLeaves` have the exact conclusions of the existing reduction. Their inputs are the two reformulated leaf propositions and the unchanged G0, G1, and G2 propositions.

The printed theorems remain hypotheses. These are equivalences and conditional corollaries, not proofs of Shimura's or Faltings's theorems. The remaining geometric and Tate readings are not silently discharged by the reformulation.

Sources: Shimura 1973, Theorem 1, pp. 525–526; Faltings 1983, section 5, Korollar 2, iii implies i, p. 361. The weight-two coefficient normalization is also Diamond–Shurman, Proposition 5.3.1.

## What remains precisely

- **S1:** the standard scheme model of `X0(M)` over the rationals, its rational cusp at infinity, and the identification of its function field with `Q(j, j_M)` and its cusp expansion.
- **S2:** the scheme-level identification of a one-dimensional abelian variety with a Weierstrass elliptic curve, and identification of its invariant differential line.
- **S3:** the canonical modular map and quotient map in those scheme models, their rational coordinate expansions, and the geometric differential pullback yielding the stated theta identity.
- **S4 beyond the arithmetic model:** the interpretation of the one-dimensional zeta factor of the abelian quotient. No abelian-variety zeta functor is constructed here.
- **F1 beyond the arithmetic model:** proof of `GoodReductionFrobeniusTraceDictionaryQ`, including Frobenius trace and determinant and good-reduction specialization. No canonical Frobenius lift is constructed here.
- **F2 beyond function fields:** obtaining the pointed function-field embedding from the source's scheme-level abelian-variety isogeny. No scheme-to-function-field functor is asserted.
- The original two printed leaves and **G0, G1, G2** remain hypotheses. No conductor equality or new geometric modular parametrization is proved.

## Verification

`ProofAudit.txt` contains the exact Lean types and individual kernel axiom reports of all 83 proved theorems, followed by the relevant model and proposition definitions. The diagnostic declarations were checked separately from the deliverable source. Every theorem's report is `[propext, Classical.choice, Quot.sound]`.

Axiom reports do not discharge proposition hypotheses. In particular, the Frobenius proposition remains an explicit input in the two genuine Tate-determinant comparison theorems.

The verified Lean source has SHA-256 `6aee62a9b33f24db9e7700f582a30b092141412cf947df26e042f661502d0ce1` and size 75,590 bytes.
