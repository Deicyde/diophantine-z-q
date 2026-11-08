---
article_id: af_9733bddb620eedb72f165079
declaration: theorem
origin: background
---

# Tails of the twisted harmonic sums

Let $q\ge1$, let $\chi$ be a nonprincipal Dirichlet character modulo $q$, and let $\sigma\ge1$
be real. For all integers $K\ge N\ge1$,
$$\Bigl|\sum_{N<n\le K}\frac{\chi(n)}{n^{\sigma}}\Bigr|\le\frac{2q}{N},$$
and if moreover $N\ge3$,
$$\Bigl|\sum_{N<n\le K}\frac{\chi(n)\log n}{n^{\sigma}}\Bigr|\le\frac{2q\log N}{N}.$$

**Proof sketch.** Summation by parts: if every partial sum $\sum_{N<n\le m}c_n$ has absolute
value at most $B$ and $f\ge0$ is nonincreasing on $n\ge N+1$, then
$\bigl|\sum_{N<n\le K}c_nf(n)\bigr|\le B\,f(N+1)$. Take $c_n=\chi(n)$, so $B=q$ by the
bound on character sums, and $f(n)=n^{-\sigma}$, respectively $f(n)=\log n\cdot n^{-\sigma}$,
which is nonincreasing for $n\ge3$ because $\log t/t$ decreases on $[e,\infty)$ and
$t^{1-\sigma}$ is nonincreasing. Then $q(N+1)^{-\sigma}\le q/(N+1)\le2q/N$, and
$q\log(N+1)(N+1)^{-\sigma}\le q\log(N+1)/(N+1)\le q\log N/N\le2q\log N/N$.

## Depends on

None.

## Proof depends on

- [Character sums are bounded by the modulus](character-sums.md)

## Sources

- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
- [Apostol, Chapter 4](../../../sources/progressions-locators.md#apostol-chapter-4)
