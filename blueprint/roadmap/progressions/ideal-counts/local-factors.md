---
article_id: af_8d805a936f9ffd67196f4d85
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.localEps, ZInQ.Progressions.localEps_mem, ZInQ.Progressions.idealCount_prime_pow, ZInQ.Progressions.exists_localFactor, ZInQ.Progressions.eq_localEps_of_idealCount_prime_pow, ZInQ.Progressions.idealCount_prime_pow_cases, ZInQ.Progressions.IdealCount.tsum_term_idealCount_prime_pow, ZInQ.Progressions.IdealCount.norm_localEps_le_one
---

# Ideal counts at prime powers in a quadratic field

Let $K$ be a number field of degree $2$ and $p$ a prime. Put $\varepsilon_p=a_K(p)-1$. Then
$\varepsilon_p\in\{-1,0,1\}$, and for every $k\ge0$
$$a_K(p^k)=\sum_{j=0}^k\varepsilon_p^{\,j} ;$$
conversely, $\varepsilon_p$ is the only integer with this property. Equivalently, for every
complex $s$ with $\mathrm{Re}\,s>0$,
$$\sum_{k\ge0}a_K(p^k)p^{-ks}=(1-p^{-s})^{-1}(1-\varepsilon_pp^{-s})^{-1}.$$

**Proof sketch.** The ideals of norm $p^k$ are the products $\prod_i\mathfrak p_i^{a_i}$ of the
primes $\mathfrak p_i$ above $p$ with $\sum_ia_if_i=k$, where $f_i$ is the residue degree:
unique factorization gives a bijection with these exponent vectors. Write
$p\mathcal O_K=\prod_i\mathfrak p_i^{e_i}$; then $\sum_ie_if_i=2$. Three cases remain. Split:
two primes of norm $p$, so $a_K(p^k)=k+1$ and $\varepsilon_p=1$. Inert: one prime of norm
$p^2$, so $a_K(p^k)$ is $1$ for even $k$ and $0$ for odd $k$, and $\varepsilon_p=-1$.
Ramified: one prime of norm $p$, so $a_K(p^k)=1$ and $\varepsilon_p=0$. In each case the
formula holds; the case $k=1$ shows that $\varepsilon_p$ is determined. Since
$|\varepsilon_p|\le1$ and $|p^{-s}|<1$, the Euler factor is the Cauchy product of two
geometric series.

## Depends on

- [The ideal counting function](ideal-count.md)

## Sources

- [Marcus, Chapter 3](../../../sources/progressions-locators.md#marcus-chapter-3)
