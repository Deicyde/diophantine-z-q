---
article_id: af_1bd828f44c272f8fab347e55
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Density.phi_CL_lower, ZInQ.Density.summable_vonMangoldt_div_rpow
---

# The main term: the Dirichlet series of $C_L$

For a set $S$ of natural numbers and real $x>1$ put $\Phi_S(x)=\sum_{n\in S}(\log n)/n^x$. For every
$L$ there is a constant $K_L$ such that
$$\Phi_{C_L}(x)\ge\frac{\delta_L}{x-1}-K_L\qquad\text{for all }x\in(1,2].$$

**Proof sketch.** This is Dirichlet's theorem in residue classes, in the form Mathlib proves it:
for a unit $a$ modulo $M$, the series $\sum_{n\equiv a}\Lambda(n)/n^x$ is at least
$\varphi(M)^{-1}/(x-1)-C_a$ on $(1,2]$. Sum over the $\#A_L$ unit classes $a\in A_L$; on primes
$\Lambda(p)=\log p$, and the contribution of proper prime powers is bounded on $(1,2]$ by its
(convergent) value at exponent $1$.

## Depends on

- [The residue set $A_L$ and the primes $C_L$](residue-set.md)

## Sources

- [The main term](../../sources/density-locators.md#the-main-term)
