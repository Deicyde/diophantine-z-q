---
article_id: af_a7d3247a1721c2fdc44956a2
declaration: theorem
origin: background
---

# The factorization of $\zeta_K$

Let $q\ge1$ and let $\chi$ be a Dirichlet character modulo $q$. Let $d$ be a squarefree
integer with $d\ne1$, every prime factor of which divides $2q$, such that
$\chi(p)=\bigl(\frac dp\bigr)$ for every prime $p\nmid2q$. Let $K=\mathbb Q(\sqrt d)$ and
$\varepsilon_p=a_K(p)-1$. Then for every real $s>1$,
$$\zeta_K(s)=\zeta(s)\,L(s,\chi)\prod_{p\mid2q}\frac{1-\chi(p)p^{-s}}{1-\varepsilon_pp^{-s}},$$
the product running over the primes dividing $2q$.

**Proof sketch.** For real $s>1$ all three Dirichlet series converge absolutely and have
Euler products: the coefficients $a_K$ are multiplicative with the local factors
$(1-p^{-s})^{-1}(1-\varepsilon_pp^{-s})^{-1}$, and $\zeta(s)L(s,\chi)$ has the local factors
$(1-p^{-s})^{-1}(1-\chi(p)p^{-s})^{-1}$. For $p\nmid2q$, the prime $p$ is odd and does not
divide $d$, so $\varepsilon_p=(d/p)=\chi(p)$ by the splitting law and the local factors agree.
The quotient of the two Euler products is therefore the finite product over $p\mid2q$.
(Here $\chi(p)=0$ for $p\mid q$, so only $p=2\nmid q$ contributes a nontrivial numerator.)

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
