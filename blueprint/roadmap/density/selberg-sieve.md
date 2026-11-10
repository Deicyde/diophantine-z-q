---
article_id: af_310d372144545a2faaed5520
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: SelbergSieve.selberg_bound_simple, SelbergSieve.selbergTerms, SelbergSieve.selbergBoundingSum, SelbergSieve.selbergBoundingSum_pos, SelbergSieve.selbergWeights, SelbergSieve.selbergUbSieve, SelbergSieve.selberg_bound_simple_mainSum, SelbergSieve.selberg_bound_simple_errSum, SelbergSieve.selberg_bound_weights, SelbergSieve.selberg_bound_muPlus
---

# The Selberg sieve bound

Let $\mathcal A$ be a finite set of natural numbers with nonnegative weights $a_n$ and total mass
$X$, let $P$ be a squarefree product of primes, let $\nu$ be a multiplicative function with
$0<\nu(q)<1$ for the primes $q\mid P$, and let $y\ge1$ be the level. Put
$R_d=\sum_{n\in\mathcal A,\,d\mid n}a_n-\nu(d)X$, $g(l)=\nu(l)\prod_{q\mid l}(1-\nu(q))^{-1}$ and
$S=\sum_{l\mid P,\ l^2\le y}g(l)$. Then $S>0$ and
$$\sum_{\substack{n\in\mathcal A\ \gcd(n,P)=1}}a_n\;\le\;\frac XS+\sum_{\substack{d\mid P\ d\le y}}3^{\omega(d)}|R_d| .$$

This is Selberg's upper bound sieve. The Lean proof is the one of the PrimeNumberTheoremAnd project
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, by Arend Mellendijk), vendored unchanged
except for its import lines under the Apache License 2.0, and built on Mathlib's sieve structures.

**Proof sketch.** Choose the Selberg weights $\lambda_d$ ($d\mid P$, $d^2\le y$, $\lambda_1=1$) that
minimize the quadratic form of the main term; then $\mu^+(d)=\sum_{[d_1,d_2]=d}\lambda_{d_1}\lambda_{d_2}$
is an upper bound sieve, the main term equals $X/S$ after diagonalization, $|\lambda_d|\le1$, and
$|\mu^+(d)|\le3^{\omega(d)}$, which bounds the error term.

## Depends on

None.

## Sources

- [The vendored Selberg sieve](../../sources/density-locators.md#the-vendored-selberg-sieve)
