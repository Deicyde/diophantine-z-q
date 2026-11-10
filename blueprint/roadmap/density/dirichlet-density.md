---
article_id: af_21cb7e7e6c0f16fb2fd2db0a
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Density.primesRelUpperDensityPos_of_dirichlet
---

# Dirichlet density gives relative upper density

Let $S$ be a set of natural numbers, and let $\eta>0$ and $K$ be reals with
$$\Phi_S(x)\ge\frac\eta{x-1}-K\qquad\text{for all }x\in(1,2].$$
Then $S$ has positive relative upper density in the primes: there is $c>0$ with
$\#(S\cap[0,N])\ge c\,\pi(N)$ for infinitely many $N$.

This is Proposition 5.3 of the research note (a positive lower Dirichlet density in the von Mangoldt
normalisation gives a positive upper relative density).

**Proof sketch.** Suppose not. Then for every $c>0$ eventually $\#(S\cap[0,N])<c\,\pi(N)$, and with
Chebyshev's bound $\pi(N)\le(\log4+\varepsilon)N/\log N$ this gives $\theta_S(N)\le\#(S\cap[0,N])\log N\le\kappa N$
for large $N$ with $\kappa$ as small as we like, hence $\theta_S(N)\le\kappa N+B$ for all $N$. Abel
summation gives $\Phi_S(x)\le\kappa x/(x-1)+B$, which contradicts the lower bound as $x\to1^+$ once
$2\kappa<\eta$.

## Depends on

- [Szemerédi's theorem in the primes](../green-tao/dense-form.md)
- [Abel summation for $\Phi_S$](abel-summation.md)

## Sources

- [Assembly](../../sources/density-locators.md#assembly)
