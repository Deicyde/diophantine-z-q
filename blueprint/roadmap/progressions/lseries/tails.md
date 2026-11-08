---
article_id: af_9733bddb620eedb72f165079
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.norm_sum_mul_antitone_le, ZInQ.Progressions.norm_sum_Ioc_char_div_cpow_le, ZInQ.Progressions.norm_sum_Ioc_char_div_cpow_le_two_mul, ZInQ.Progressions.norm_sum_Ioc_char_log_div_cpow_le, ZInQ.Progressions.norm_sum_Ioc_char_log_div_cpow_le_two_mul, ZInQ.Progressions.norm_LFunction_sub_sum_le, ZInQ.Progressions.norm_tail_le, ZInQ.Progressions.norm_LSeries_logMul_sub_sum_le, ZInQ.Progressions.norm_tail_log_le
---

# Tails of the twisted harmonic sums

Let $q\ge1$ and let $\chi$ be a nonprincipal Dirichlet character modulo $q$. For all integers
$N,K\ge0$ and real $\sigma$:

1. if $\sigma\ge0$, then
   $\bigl|\sum_{N<n\le K}\chi(n)n^{-\sigma}\bigr|\le q\,(N+1)^{-\sigma}$; if $\sigma\ge1$ and
   $N\ge1$, this is at most $2q/N$;
2. if $\sigma\ge1$ and $N\ge2$, then
   $\bigl|\sum_{N<n\le K}\chi(n)\log n\cdot n^{-\sigma}\bigr|\le q\log(N+1)\,(N+1)^{-\sigma}$;
   if moreover $N\ge3$, this is at most $2q\log N/N$.

For real $\sigma>1$ the same bounds hold for the infinite tails: with $L(\sigma,\chi)$ the value
of the $L$-function and $N\ge0$,
$$\Bigl|L(\sigma,\chi)-\sum_{1\le n\le N}\frac{\chi(n)}{n^{\sigma}}\Bigr|\le q\,(N+1)^{-\sigma},$$
which is at most $2q/N$ for $N\ge1$; and for $N\ge2$,
$$\Bigl|\sum_{n\ge1}\frac{\chi(n)\log n}{n^{\sigma}}
-\sum_{1\le n\le N}\frac{\chi(n)\log n}{n^{\sigma}}\Bigr|\le q\log(N+1)\,(N+1)^{-\sigma},$$
which is at most $2q\log N/N$ for $N\ge3$.

**Proof sketch.** Summation by parts: if every partial sum $\sum_{N<n\le m}c_n$ has absolute
value at most $B$ and $f\ge0$ is nonincreasing on $n\ge N+1$, then
$\bigl|\sum_{N<n\le K}c_nf(n)\bigr|\le B\,f(N+1)$. Take $c_n=\chi(n)$, so $B=q$ by the
bound on character sums, and $f(n)=n^{-\sigma}$, respectively $f(n)=\log n\cdot n^{-\sigma}$,
which is nonincreasing for $n\ge3$ because $\log t/t$ decreases on $[e,\infty)$ and
$t^{1-\sigma}$ is nonincreasing. Then $q(N+1)^{-\sigma}\le q/(N+1)\le2q/N$, and
$q\log(N+1)(N+1)^{-\sigma}\le q\log(N+1)/(N+1)\le q\log N/N\le2q\log N/N$ for $N\ge3$. For
$\sigma>1$ both series converge absolutely (the first to $L(\sigma,\chi)$), and a bound
on every finite tail $\sum_{N<n\le K}$ passes to the limit $K\to\infty$.

## Depends on

None.

## Proof depends on

- [Character sums are bounded by the modulus](character-sums.md)

## Sources

- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
- [Apostol, Chapter 4](../../../sources/progressions-locators.md#apostol-chapter-4)
