---
article_id: af_e280a7ecf164acebf9c98268
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.sum_nonprime_vonMangoldt_div_le_two, ZInQ.Progressions.sum_Ioc_nonprime_vonMangoldt_div_le, ZInQ.Progressions.sum_vonMangoldt_mul_le_sum_primePow, ZInQ.Progressions.sum_Icc_log_div_mul_pred_le'
---

# Higher prime powers contribute little

For every integer $N\ge0$,
$$\sum_{\substack{n\le N\\ n\text{ not prime}}}\frac{\Lambda(n)}{n}\le2 ,$$
that is, the prime powers $p^k$ with $k\ge2$ contribute at most $2$ to
$\sum_{n\le N}\Lambda(n)/n$. Moreover, for all integers $Y\ge1$ and $M\ge0$, with
$s=\lfloor\sqrt Y\rfloor$,
$$\sum_{\substack{Y<n\le M\\ n\text{ not prime}}}\frac{\Lambda(n)}{n}
\le\frac{\log s+2+2\log4}{s}.$$

**Proof sketch.** A sum of $\Lambda(n)h(n)$ with $h\ge0$ is at most the double sum of
$\log p\cdot h(p^k)$ over primes $p$ and exponents $k$ that cover its prime powers. The
telescoping bound
$\sum_{s<n\le N}\log n/(n(n-1))\le(\log s+2)/s-(\log N+2)/N$ for $1\le s\le N$ holds term by
term. For the first bound, the sum is at most
$\sum_p\sum_{k\ge2}\log p/p^k\le\sum_p\log p/(p(p-1))\le\sum_{m\ge2}\log m/(m(m-1))\le2$, by
the telescoping bound at $s=1$. For the second, a prime $p\le s$ contributes at most
$2\log p/Y$, since its powers above $Y$ form a geometric series with ratio $1/p\le1/2$
starting below $1/Y$; these primes give at most $2\theta(s)/Y\le2\log4\cdot s/Y\le2\log4/s$.
A prime $p>s$ contributes at most $\log p/(p(p-1))$, and these primes give at most
$\sum_{n>s}\log n/(n(n-1))\le(\log s+2)/s$.

## Depends on

None.

## Sources

- [Apostol, Chapter 4](../../../sources/progressions-locators.md#apostol-chapter-4)
