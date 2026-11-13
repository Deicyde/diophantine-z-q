---
article_id: af_d1a98506389da60945ad8096
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Density.goodPrimeDensity_of_uniformBadBound, ZInQ.Density.card_TL_le, ZInQ.Density.exists_L, ZInQ.Density.eventually_rpow_mul_log_le
---

# Theorem D: the density statement from the uniform bound

Assume the uniform bad-prime bound. Then the good slope primes have positive relative upper density
in the primes.

The proof goes through Theorem D of the research note: for a suitable $L$, the set $G^*_L=C_L\setminus T_L$
of good slope primes satisfies $\Phi_{G^*_L}(x)\ge\eta_L/(x-1)-K$ on $(1,2]$ with $\eta_L>0$, a positive
lower Dirichlet density. The Lean proof applies this to the larger set of all good slope primes
directly.

**Proof sketch.** Let $A,N_1$ be the constants of the uniform bound and choose $L\ge5$ with
$\log L\ge16A\log4$. For $N\ge\max(N_1,2)$, the uniform bound for the primes $L<\ell\le N^{1/4}$, summed
with the prime tail, and the lattice count for the primes $\ell>N^{1/4}$ give
$\#(T_L\cap[0,N])\le\alpha_LN/\log N+20N^{3/4}$ with $\alpha_L=3A\log4/(L\log L)\le\delta_L/2$. With
$\varepsilon=\delta_L/4$, eventually $\theta_{T_L}(N)\le(\alpha_L+\varepsilon)N$, so Abel summation gives
$\Phi_{T_L}(x)\le(\alpha_L+\varepsilon)x/(x-1)+B$. Since $C_L\setminus T_L$ consists of good slope primes,
$\Phi_G\ge\Phi_{C_L}-\Phi_{T_L}$, and the main term gives
$\Phi_G(x)\ge(\delta_L-\alpha_L-\varepsilon)/(x-1)-K'$ with $\delta_L-\alpha_L-\varepsilon\ge\delta_L/4>0$.
Dirichlet density gives relative upper density.

## Depends on

- [The density statement for good slope primes](good-prime-density.md)
- [The uniform bound for the primes bad at a medium $\ell$](uniform-bad-bound.md)

## Proof depends on

- [A subset of good slope primes](good-subset.md)
- [The main term: the Dirichlet series of $C_L$](main-term.md)
- [The residue set $A_L$ and the primes $C_L$](residue-set.md)
- [The primes bad at a large $\ell$](lattice-count.md)
- [The prime tail $\sum_{\ell>L}\ell^{-2}$](prime-tail.md)
- [Abel summation for $\Phi_S$](abel-summation.md)
- [Dirichlet density gives relative upper density](dirichlet-density.md)

## Sources

- [Assembly](../../sources/density-locators.md#assembly)
