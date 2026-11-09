# Locators for the progressions chapter

The progressions chapter replaces the explicit progression estimate of Bennett, Martin,
O'Bryant and Rechnitzer, which the manuscript cites in the proof of Proposition 12.1, by a
self-contained effective form of Dirichlet's theorem. Its statements are textbook results,
made explicit; the sources below are cited at the level of chapters. The quantitative
constants are this blueprint's own and are not taken from the sources.

## Apostol, Chapter 3

T. M. Apostol, *Introduction to Analytic Number Theory*, Springer, 1976, Chapter 3
(averages of arithmetical functions): Euler's summation formula and the partial sums
$\sum_{n\le x}1/n$ and $\sum_{n\le x}\log n/n$ used for the bounds on $L(\sigma,\chi)$ and
its derivative.

## Apostol, Chapter 4

Apostol, Chapter 4 (elementary theorems on the distribution of primes): Chebyshev's
functions $\psi$ and $\theta$, Abel's identity, the formula
$\log\lfloor x\rfloor!=\sum_{n\le x}\Lambda(n)\lfloor x/n\rfloor$ and the estimate
$\sum_{n\le x}\Lambda(n)/n=\log x+O(1)$ (Mertens' first theorem).

## Apostol, Chapter 6

Apostol, Chapter 6 (finite abelian groups and their characters): Dirichlet characters,
the orthogonality relations, sums involving Dirichlet characters (the bound $q$ for
character sums and the tails of $\sum\chi(n)/n$ and $\sum\chi(n)\log n/n$), and the
nonvanishing of $L(1,\chi)$ for real $\chi$.

## Apostol, Chapter 7

Apostol, Chapter 7 (Dirichlet's theorem on primes in arithmetic progressions): the
asymptotic formula for $\sum_{p\le x,\ p\equiv h\ (\mathrm{mod}\ k)}\log p/p$, proved from
Mertens' theorem, orthogonality and the identity relating
$L(1,\chi)\sum_{n\le x}\chi(n)\Lambda(n)/n$ to $\sum_{n\le x}\chi(n)\log n/n$; the route of
the counting section follows it with explicit constants.

## Apostol, Chapter 9

Apostol, Chapter 9 (quadratic residues and the quadratic reciprocity law): Legendre and
Jacobi symbols, the supplementary laws for $-1$ and $2$, and reciprocity, used in the
classification of real characters.

## Apostol, Chapter 11

Apostol, Chapter 11 (Dirichlet series and Euler products): Euler products of
multiplicative functions, and differentiation of Dirichlet series term by term in the
half-plane of absolute convergence.

## Davenport, Chapter 1

H. Davenport, *Multiplicative Number Theory*, third edition (revised by H. L. Montgomery),
Graduate Texts in Mathematics 74, Springer, 2000, Chapter 1 (primes in arithmetic
progression): Dirichlet's proof, where the nonvanishing of $L(1,\chi)$ for real $\chi$
comes from the class number of a quadratic field.

## Davenport, Chapter 4

Davenport, Chapter 4 (primes in arithmetic progression: the general modulus): characters
to a general modulus, their decomposition over the prime powers of the modulus, and the
nonvanishing of $L(1,\chi)$ for complex $\chi$ by the product
$\zeta^3|L(\cdot,\chi)|^4|L(\cdot,\chi^2)|\ge1$.

## Davenport, Chapter 5

Davenport, Chapter 5 (primitive characters): real characters, and the description of the
real primitive characters by Kronecker symbols, which the classification of real
characters follows on primes not dividing $2q$.

## Davenport, Chapter 6

Davenport, Chapter 6 (Dirichlet's class-number formula): the factorization of the Dedekind
zeta function of a quadratic field as $\zeta(s)L(s,\chi)$ and the formula expressing
$L(1,\chi)$ through the class number, the regulator and the number of roots of unity.

## Marcus, Chapter 2

D. A. Marcus, *Number Fields*, Springer, 1977, Chapter 2 (number fields and number rings):
quadratic fields, their rings of integers and discriminants.

## Marcus, Chapter 3

Marcus, Chapter 3 (prime decomposition in number rings): the relation
$\sum_ie_if_i=n$, the decomposition of primes in quadratic fields, and the Kummer–Dedekind
criterion.

## Marcus, Chapter 5

Marcus, Chapter 5 (the ideal class group and the unit group): roots of unity, Dirichlet's
unit theorem and the regulator.

## Marcus, Chapter 7

Marcus, Chapter 7 (the Dedekind zeta function and the class number formula): the Dedekind
zeta function as the Dirichlet series of ideal counts, its residue at $s=1$, and its
factorization for quadratic fields. Mathlib's class number formula
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) follows this chapter.
