---
article_id: af_e6df458181c1c890ae0ec00a
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.mertensSum, ZInQ.Progressions.abs_mertensSum_sub_log_le, ZInQ.Progressions.log_sub_two_le_mertensSum, ZInQ.Progressions.mertensSum_le_log_add_three, ZInQ.Progressions.psi_le_three_mul, ZInQ.Progressions.psi_div_le_three
---

# Mertens' first theorem

Let $\Lambda$ be the von Mangoldt function and $\psi(x)=\sum_{n\le x}\Lambda(n)$. For every
real $x\ge0$, $\psi(x)\le3x$. For every real $x\ge1$,
$$\log x-2\le\sum_{n\le x}\frac{\Lambda(n)}{n}\le\log x+3,\qquad\text{so}\qquad
\Bigl|\sum_{n\le x}\frac{\Lambda(n)}{n}-\log x\Bigr|\le3 .$$

**Proof sketch.** Chebyshev's bound $\psi(x)\le\log4\cdot x+2\sqrt x\log x$ for $x\ge1$,
with $\log x\le2\sqrt x/e$ (from $\log t\le t-1$ at $t=\sqrt x/e$) and $4/e\le1.5$, gives
$\psi(x)\le(\log4+1.5)x\le3x$; for $x<2$, $\psi(x)=0$. Let $N=\lfloor x\rfloor\ge1$. Since
$\log n=\sum_{d\mid n}\Lambda(d)$,
$$\log N!=\sum_{d\le N}\Lambda(d)\Bigl\lfloor\frac Nd\Bigr\rfloor
=N\sum_{d\le N}\frac{\Lambda(d)}d-\sum_{d\le N}\Lambda(d)\Bigl\{\frac Nd\Bigr\},$$
and the last sum lies in $[0,\psi(N)]$. With $N\log N-N\le\log N!\le N\log N$ and
$\psi(N)\le3N$, this gives $\log N-1\le\sum_{d\le N}\Lambda(d)/d\le\log N+3$. Finally
$\log N\le\log x\le\log N+1$, since $x/N<2$.

## Depends on

None.

## Sources

- [Apostol, Chapter 4](../../../sources/progressions-locators.md#apostol-chapter-4)
