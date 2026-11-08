---
article_id: af_e6df458181c1c890ae0ec00a
declaration: theorem
origin: background
---

# Mertens' first theorem

Let $\Lambda$ be the von Mangoldt function. For every real $x\ge1$,
$$\Bigl|\sum_{n\le x}\frac{\Lambda(n)}{n}-\log x\Bigr|\le6 .$$

**Proof sketch.** Let $N=\lfloor x\rfloor\ge1$. Since $\log n=\sum_{d\mid n}\Lambda(d)$,
$$\log N!=\sum_{d\le N}\Lambda(d)\Bigl\lfloor\frac Nd\Bigr\rfloor
=N\sum_{d\le N}\frac{\Lambda(d)}d-\sum_{d\le N}\Lambda(d)\Bigl\{\frac Nd\Bigr\},$$
and the last sum lies in $[0,\psi(N)]$. With $N\log N-N+1\le\log N!\le N\log N$ and
Chebyshev's bound $\psi(N)\le(\log4+4)N\le6N$, this gives
$\log N-1\le\sum_{d\le N}\Lambda(d)/d\le\log N+6$. Finally
$0\le\log x-\log N<\log2<1$.

## Depends on

None.

## Sources

- [Apostol, Chapter 4](../../../sources/progressions-locators.md#apostol-chapter-4)
