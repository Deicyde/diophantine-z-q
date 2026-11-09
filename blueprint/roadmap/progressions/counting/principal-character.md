---
article_id: af_196a7d0bc107ac1eb0ad0837
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.log_div_sub_le_re_twistedSum_one_sub, ZInQ.Progressions.twistedSum_one_eq, ZInQ.Progressions.sum_nonunit_vonMangoldt_div_le_log
---

# The principal character

Let $q\ge1$ and let $1\le y\le x$ be real. Then
$$\sum_{\substack{y<n\le x\\ \gcd(n,q)=1}}\frac{\Lambda(n)}{n}\ge\log\frac xy-6-\log q ;$$
the left side is $S_{\chi_0}(x)-S_{\chi_0}(y)$ for the principal character $\chi_0$ modulo
$q$. Moreover, for every integer $N\ge0$,
$\sum_{n\le N,\ \gcd(n,q)>1}\Lambda(n)/n\le\log q$.

**Proof sketch.** By Mertens' first theorem,
$\sum_{y<n\le x}\Lambda(n)/n\ge(\log x-2)-(\log y+3)\ge\log(x/y)-6$. The terms with
$\gcd(n,q)>1$ and $\Lambda(n)\ne0$ are the powers $p^k$ of the primes $p\mid q$, and all of
them together contribute at most
$\sum_{p\mid q}\sum_{k\ge1}\log p/p^k=\sum_{p\mid q}\log p/(p-1)\le\sum_{p\mid q}\log p\le\log q$.

## Depends on

None.

## Proof depends on

- [Mertens' first theorem](mertens.md)

## Sources

- [Apostol, Chapter 7](../../../sources/progressions-locators.md#apostol-chapter-7)
