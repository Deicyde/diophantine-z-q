---
article_id: af_ea28059799ebdf10c248728c
---

# The field, the curve and division polynomials

Everything takes place over $K_0=\mathbb Q(s)$, $s^2=2$, written in the basis $1,s$, so that
each field equation is two rational equations. A field element is nonzero exactly when its
norm is, which is how one rational witness expresses every nonvanishing condition; the pair
arithmetic and the inverse witnesses are set up in the specification chapter
([pair arithmetic](../../syntax/field-pair-arithmetic.md),
[inverse witnesses](../../syntax/nonzero-gadgets.md)).

- [The field $K_0=\mathbb Q(\sqrt2)$](quadratic-field.md)

The handful of explicit identities and sign facts used throughout (the square of $d$, powers of
$\epsilon=1+s$, $\delta=\epsilon^4d$, norms, total positivity of $d$ and $\delta$) are collected in one
closed statement.

- [Explicit identities in $K_0$](explicit-identities.md)

The curve is $E:y^2=x^3-d^2x$ with $d=75-53s$, and the base point is $P_0$; that its
coordinates satisfy the curve equation is a closed identity in $K_0$.

- [The generator curve $E$](generator-curve.md)
- [The coordinates of $P_0$ satisfy the curve equation](generator-point-equation.md)
- [The point $P_0$](generator-point.md)

Codes are injective, negation flips the two ordinate coordinates, and the code of a sum of
multiples of $P_0$ is the code of the summed index.

- [Elementary properties of codes](point-code-properties.md)

## Division polynomials

Fixed multiples $[n]Q$, for fixed integers $n$ that may have millions of digits, are
expressed by the normalized division polynomials of the specification
([their definition](../../syntax/division-polynomials.md)). The specification chapter states
their classical multiplication formulas as a proposition
([the multiplication-by-n formulas](../../syntax/division-polynomial-multiplication.md)) and
derives from it the semantics of the fixed-scalar templates
([fixed-scalar semantics](../../syntax/fixed-scalar-semantics.md)). Here the proposition is
proved as a background theorem, and it gives the fixed point codes $\iota(n)$. The recursion is
only ever used symbolically. The proof goes through Jacobian coordinates: the triples
$(\phi_n,\omega_n,\psi_n)$ satisfy exact doubling and adding identities, first at the generic point
of the curve, where no division polynomial vanishes, and an induction on $n$ shows that these
triples represent the multiples $[n]P$.

- [Division polynomials compute multiples](division-polynomial-multiples.md)
- [Fixed point codes by division polynomials](fixed-point-codes.md)

## Arithmetic of $\mathbb Z[\sqrt2]$

The descent uses unique factorization in $\mathbb Z[s]$, its units $\pm(1+s)^k$, and the two
special primes: $(s)$ above $2$ and $(d)=(\delta)$ above $7$.

- [$\mathbb Z[\sqrt2]$ is a principal ideal domain](integers-pid.md)
- [Units of $\mathbb Z[\sqrt2]$](units.md)
- [Residue computations modulo seven](residue-checks.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](special-primes.md)
- [A dyadic valuation computation](dyadic-valuation.md)
