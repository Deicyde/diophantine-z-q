---
article_id: af_70c61a80fd63807e9c41e9ae
declaration: theorem
origin: background
---

# The splitting law in $\mathbb Q(\sqrt d)$

Let $d$ be a squarefree integer with $d\ne1$, $K=\mathbb Q(\sqrt d)$, and let $p$ be an odd
prime with $p\nmid d$. Then the local sign $\varepsilon_p=a_K(p)-1$ is the Legendre symbol:
$$\varepsilon_p=\Bigl(\frac dp\Bigr).$$

**Proof sketch.** The order $\mathbb Z[\sqrt d]=\mathbb Z[X]/(X^2-d)$ has index $1$ or $2$ in
$\mathcal O_K$, prime to $p$, so the Kummer–Dedekind theorem describes $p\mathcal O_K$ by the
factorization of $X^2-d$ modulo $p$, which is separable since $p\nmid2d$. If $d$ is a
nonzero square modulo $p$, then $X^2-d$ has two distinct roots, $p$ splits and
$a_K(p)=2$. Otherwise $X^2-d$ is irreducible, $p$ is inert and $a_K(p)=0$.

## Depends on

- [The quadratic field $\mathbb Q(\sqrt d)$](../quadratic-fields/quadratic-field.md)
- [The ideal counting function](ideal-count.md)

## Proof depends on

- [Ideal counts at prime powers in a quadratic field](local-factors.md)

## Sources

- [Marcus, Chapter 3](../../../sources/progressions-locators.md#marcus-chapter-3)
