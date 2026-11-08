---
article_id: af_8d805a936f9ffd67196f4d85
declaration: theorem
origin: background
---

# Ideal counts at prime powers in a quadratic field

Let $K$ be a number field of degree $2$ and $p$ a prime. Put $\varepsilon_p=a_K(p)-1$. Then
$\varepsilon_p\in\{-1,0,1\}$, and for every $k\ge0$
$$a_K(p^k)=\sum_{j=0}^k\varepsilon_p^{\,j} .$$
Equivalently, for real $s>0$,
$\sum_{k\ge0}a_K(p^k)p^{-ks}=(1-p^{-s})^{-1}(1-\varepsilon_pp^{-s})^{-1}$.

**Proof sketch.** The ideals of norm $p^k$ are the products of the primes above $p$ with
total norm $p^k$. Write $p\mathcal O_K=\prod_i\mathfrak p_i^{e_i}$ with residue degrees
$f_i$; then $\sum_ie_if_i=2$. Three cases remain. Split: two primes of norm $p$, so
$a_K(p^k)=k+1$ and $\varepsilon_p=1$. Inert: one prime of norm $p^2$, so $a_K(p^k)$ is $1$
for even $k$ and $0$ for odd $k$, and $\varepsilon_p=-1$. Ramified: one prime of norm $p$,
so $a_K(p^k)=1$ and $\varepsilon_p=0$. In each case the formula holds.

## Depends on

- [The ideal counting function](ideal-count.md)

## Sources

- [Marcus, Chapter 3](../../../sources/progressions-locators.md#marcus-chapter-3)
