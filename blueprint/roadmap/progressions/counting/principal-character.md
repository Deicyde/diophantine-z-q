---
article_id: af_196a7d0bc107ac1eb0ad0837
declaration: theorem
origin: background
---

# The principal character

Let $q\ge1$ and let $1\le y\le x$ be real. Then
$$\sum_{\substack{y<n\le x\\ \gcd(n,q)=1}}\frac{\Lambda(n)}{n}\ge\log\frac xy-12-\log q .$$

**Proof sketch.** By Mertens' first theorem,
$\sum_{y<n\le x}\Lambda(n)/n\ge(\log x-6)-(\log y+6)$. The terms with $\gcd(n,q)>1$ and
$\Lambda(n)\ne0$ are the powers $p^k$ of the primes $p\mid q$, and they contribute at most
$\sum_{p\mid q}\sum_{k\ge1}\log p/p^k=\sum_{p\mid q}\log p/(p-1)\le\sum_{p\mid q}\log p\le\log q$.

## Depends on

None.

## Proof depends on

- [Mertens' first theorem](mertens.md)

## Sources

- [Apostol, Chapter 7](../../../sources/progressions-locators.md#apostol-chapter-7)
