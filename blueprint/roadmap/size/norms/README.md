---
article_id: af_5d00aba1d97dea6b4835af52
---

# Norms, division polynomials and the finite constructors

Integer polynomials are measured by total degree and coefficient $\ell^1$ norm, and pairs
$(a,b)$ representing $a+bs$ over a polynomial ring by the weighted norm
$\|a\|_1+2\|b\|_1$. Every coefficient is bounded by the $\ell^1$ norm, so a norm bound is a
coefficient bound.

- [Coefficient norms and degrees](l1-norm.md)
- [Elementary estimates for the coefficient norm](l1-norm-estimates.md)
- [Substitution and renaming bounds](substitution-bounds.md)
- [The weighted pair norm](pair-norm.md)

The normalized division polynomials, evaluated at the formal point
$(x_0+x_1s,y_0+y_1s)$, satisfy $\deg f_n\le(n+1)^3$ and $\|f_n\|\le2^{100(n+1)^3}$ by strong
induction: the cubic exponents leave a slack of at least nine in the even recurrence and
ten in the odd one, which absorbs the fixed factors.

- [Size of the division polynomials](division-polynomial-size.md)

The guard is a product over the false triples in the box $[-T,T]^3$ of sums of squares
whose coefficients are the reduced coordinates of $\iota(a),\iota(b),\iota(c)$. These are
obtained from division polynomials at $P_0$ by a few field operations, each taking a size
$H$ to at most $3H^4$, which bounds every coordinate by $2^{2^{30}(T+1)^3}$.

- [Sizes under quadratic-field operations](quadratic-heights.md)
- [Heights of the codes in the guard box](coordinate-heights.md)
- [Size of the guard polynomial](guard-size.md)

For any $B\ge2^{20}$ that exceeds the occurring indices and cutoffs, each of the three
finite constructors has degree at most $B^4$ and norm at most $2^{B^8}$.

- [Uniform bounds for the finite constructors](constructor-bounds.md)
