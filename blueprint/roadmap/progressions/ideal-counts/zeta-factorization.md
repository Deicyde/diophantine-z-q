---
article_id: af_a7d3247a1721c2fdc44956a2
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod, ZInQ.Progressions.dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod_of_legendreSym, ZInQ.Progressions.dedekindZeta_eq_mul_prod_of_localEps_eq, ZInQ.Progressions.IdealCount.hasProd_dedekindZeta
---

# The factorization of $\zeta_K$

Let $K$ be a number field of degree $2$, with $\varepsilon_p=a_K(p)-1$, let $q\ge1$, and let
$\chi$ be a Dirichlet character modulo $q$ with $\varepsilon_p=\chi(p)$ for every prime
$p\nmid2q$. Then for every real $s>1$,
$$\zeta_K(s)=\zeta(s)\,L(s,\chi)\prod_{p\mid2q}\frac{1-\chi(p)p^{-s}}{1-\varepsilon_pp^{-s}},$$
the product running over the primes dividing $2q$, and $L(s,\chi)=\sum_{n\ge1}\chi(n)n^{-s}$.
More generally, for any finite set $P$ of primes with $\varepsilon_p=\chi(p)$ for every prime
$p\notin P$, the same identity holds for every complex $s$ with $\mathrm{Re}\,s>1$, with the
product over $p\in P$.

The hypothesis on $\varepsilon_p$ holds in the following situation: $d$ is an integer that is
not a square, $\mathcal O_K$ contains an element $\alpha$ with $\alpha^2=d$ (for instance
$K=\mathbb Q(\sqrt d)$), no prime $p\nmid2q$ divides $d$, and $\chi(p)=\bigl(\frac dp\bigr)$
for every prime $p\nmid2q$.

**Proof sketch.** For $\mathrm{Re}\,s>1$ all three Dirichlet series converge absolutely and
have Euler products: the coefficients $a_K$ are multiplicative with the local factors
$(1-p^{-s})^{-1}(1-\varepsilon_pp^{-s})^{-1}$, and $\zeta(s)L(s,\chi)$ has the local factors
$(1-p^{-s})^{-1}(1-\chi(p)p^{-s})^{-1}$. For $p\notin P$ the local factors agree. The
quotient of the two Euler products is therefore the finite product over $p\in P$. In the
situation of the last paragraph, a prime $p\nmid2q$ is odd and does not divide $d$, so
$\varepsilon_p=(d/p)=\chi(p)$ by the splitting law. (Here $\chi(p)=0$ for $p\mid q$, so only
$p=2\nmid q$ contributes a nontrivial numerator.) The hypothesis $q\ge1$ matters: for $q=0$
every prime divides $2q$ but the product would be empty.

## Depends on

- [The quadratic field $\mathbb Q(\sqrt d)$](../quadratic-fields/quadratic-field.md)
- [The ideal counting function](ideal-count.md)

## Proof depends on

- [Ideal counts are multiplicative](multiplicative.md)
- [Ideal counts at prime powers in a quadratic field](local-factors.md)
- [The splitting law in $\mathbb Q(\sqrt d)$](splitting-law.md)

## Sources

- [Marcus, Chapter 7](../../../sources/progressions-locators.md#marcus-chapter-7)
- [Davenport, Chapter 6](../../../sources/progressions-locators.md#davenport-chapter-6)
- [Apostol, Chapter 11](../../../sources/progressions-locators.md#apostol-chapter-11)
