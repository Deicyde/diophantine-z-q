---
article_id: af_88549e0188d4636b240bf6ea
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Density.abel_bound, ZInQ.Density.thetaS, ZInQ.Density.phiTerm, ZInQ.Density.PhiS, ZInQ.Density.abel_summation, ZInQ.Density.abel_partial_sum_le, ZInQ.Density.sum_one_div_rpow_le, ZInQ.Density.thetaS_le_log4, ZInQ.Density.thetaS_le_log_mul_card, ZInQ.Density.thetaS_le_of_eventually, ZInQ.Density.summable_phiTerm
---

# Abel summation for $\Phi_S$

For a set $S$ of natural numbers put $\theta_S(N)=\sum_{n\le N,\ n\in S}\log n$ and, for $x>1$,
$\Phi_S(x)=\sum_{n\in S}(\log n)/n^x$. Let $\kappa\ge0$ and $B$ be reals with $\theta_S(N)\le\kappa N+B$
for every $N$. Then for every $x\in(1,2]$ the series $\Phi_S(x)$ converges and
$$\Phi_S(x)\le\kappa\,\frac x{x-1}+B .$$

**Proof sketch.** Discrete partial summation writes $\sum_{n\le M}\mathbf 1_S(n)\log n\cdot n^{-x}$ as
$\theta_S(M)M^{-x}+\sum_{n<M}\theta_S(n)\bigl(n^{-x}-(n+1)^{-x}\bigr)$. Insert the bound on $\theta_S$; the
constant $B$ telescopes to at most $B$, and $\sum_n n\bigl(n^{-x}-(n+1)^{-x}\bigr)$ is at most
$\sum_{n\le M}n^{-x}\le x/(x-1)$, by Bernoulli's inequality. The partial sums are bounded and the terms
nonnegative.

## Depends on

None.

## Sources

- [Assembly](../../sources/density-locators.md#assembly)
