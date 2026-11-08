---
article_id: af_49c8761a8f7647758a045719
declaration: theorem
origin: background
---

# Partial sums of $\chi(n)\log n/n$

Let $q\ge1$, let $\chi$ be a nonprincipal Dirichlet character modulo $q$, and put
$M=\log q+3$. For every real $\sigma\ge1$ and every real $x$,
$$\Bigl|\sum_{1\le n\le x}\frac{\chi(n)\log n}{n^{\sigma}}\Bigr|\le M^2 .$$
In particular $\bigl|\sum_{n\le x}\chi(n)\log n/n\bigr|\le M^2$.

**Proof sketch.** Let $N=\max(q,3)$. The terms with $n\le N$ contribute at most
$\sum_{n\le N}\log n/n\le\tfrac12\log^2N+1$: the terms $n=2,3$ give less than $0.72$, and for
$n\ge4$, $\log n/n\le\int_{n-1}^n\log t\,dt/t$ since $\log t/t$ decreases on $[e,\infty)$.
If $x>N$, summation by parts against the character sum bound bounds the terms with
$N<n\le x$ by $q\log(N+1)(N+1)^{-\sigma}\le q\log(N+1)/(N+1)$. For $q\ge3$ this is at most
$\log(q+1)\le\log q+1$, and the total $\tfrac12\log^2q+\log q+2$ is below
$(\log q+3)^2$. For $q\le2$ the total is below $\tfrac12\log^23+1+\tfrac12\log4<9\le M^2$.

## Depends on

None.

## Proof depends on

- [Character sums are bounded by the modulus](character-sums.md)
- [Tails of the twisted harmonic sums](tails.md)

## Sources

- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
- [Apostol, Chapter 3](../../../sources/progressions-locators.md#apostol-chapter-3)
