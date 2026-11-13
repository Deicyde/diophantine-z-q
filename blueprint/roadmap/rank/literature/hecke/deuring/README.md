---
article_id: af_8d91b5ea31fc13a111110275
---

# Deuring's identity for $C_d$

Deuring's identity says that the L-series of $C_d$ has the same coefficients as the Hecke L-series
of $\psi_d$: $c_d(n)=\lambda_d(n)$ for every $n\ge1$, where $c_d(n)$ are the coefficients of the
standard Euler product of $C_d$, which are those of $L(C_d,s)$ for odd squarefree $d$. Both sides
are Euler products with quadratic local factors, so for odd squarefree $d$ it suffices to compare
them at the primes.

At $2$ and at the primes dividing $d$ both coefficients vanish. At a prime $p\equiv3\pmod4$ the
involution $x\mapsto-x$ shows that $y^2=x^3-d^2x$ has exactly $p$ affine solutions over
$\mathbb F_p$, so $c_d(p)=0$, while no Gaussian integer has norm $p$. At a prime $p\equiv1\pmod4$
the substitution $x\mapsto dx$ and quadratic reciprocity reduce the comparison, for squarefree
$d\equiv1\pmod4$, to the single curve $y^2=x^3-x$, where it is Gauss's point count.

Throughout, $c_d(n)$ are the coefficients of
[the standard Euler product](../../l-function-cd/l-series.md) and $\lambda_d(n)$ the
[Hecke coefficients](../gaussian/hecke-coefficients.md).

- [Deuring's identity for $C_d$](deuring-identity.md)
- [Deuring's identity at the primes $2$, $p\mid d$ and $p\equiv3\pmod4$](deuring-small-primes.md)
- [Deuring's identity from the Euler product and the split primes](deuring-of-euler-product.md)
- [The split primes for $C_d$ from the curve $y^2=x^3-x$](gauss-split-twist.md)
- [Deuring's identity for $d\equiv1\pmod4$ from Gauss's point count](deuring-from-gauss-count.md)
