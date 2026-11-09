---
article_id: af_49c8761a8f7647758a045719
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.norm_partialSum_log_le, ZInQ.Progressions.norm_sum_log_div_le, ZInQ.Progressions.sum_norm_char_log_div_cpow_le, ZInQ.Progressions.mul_log_succ_rpow_neg_le
---

# Partial sums of $\chi(n)\log n/n$

Let $q\ge1$, let $\chi$ be a nonprincipal Dirichlet character modulo $q$, and put
$M=\log q+3$. For every real $x$,
$$\Bigl|\sum_{1\le n\le x}\frac{\chi(n)\log n}{n}\Bigr|\le M^2 .$$
(For $x<1$ the sum is empty.)

**Proof sketch.** Since $\chi$ is nonprincipal, $q\ge2$. Let $N=\lfloor x\rfloor$. For every
real $\sigma\ge1$ and every $K$, $\sum_{n\le K}|\chi(n)\log n\cdot n^{-\sigma}|\le\log K\,(1+\log K)$, from
$\sum_{n\le K}1/n\le1+\log K$. So the terms with $n\le\min(N,q)$ contribute at most
$\log q\,(1+\log q)$. If $N>q$, the tail bound at $N=q$, $\sigma=1$ bounds the terms with
$q<n\le N$ by $q\log(q+1)/(q+1)\le\log q+1$. The total is at most
$\log^2q+2\log q+1\le(\log q+3)^2$. This is a statement about finite sums; no limit is
involved.

## Depends on

None.

## Proof depends on

- [Character sums are bounded by the modulus](character-sums.md)
- [Tails of the twisted harmonic sums](tails.md)

## Sources

- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
- [Apostol, Chapter 3](../../../sources/progressions-locators.md#apostol-chapter-3)
