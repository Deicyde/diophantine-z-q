---
article_id: af_f3a82a28bda02069dfcbcf6c
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.ellLog_ratio
---

# Full-logarithm ratios of multiples of $P_0$

Assume the Mordell-Weil hypothesis for $E/K_0$. Let $p$ be an odd prime, $\mathfrak p$ a prime
of $\mathbb Z[s]$ above $p$, and $\lambda$ the formal logarithm of $E$ over the completion
$K_{\mathfrak p}$. Let $h,u\in\mathbb Z$ with $h\ne0$ such that $[h]P_0$ and $[u]P_0$ lie in
$E_1(K_{\mathfrak p})$. Then
$$\lambda([h]P_0)\ne0\qquad\text{and}\qquad\lambda([u]P_0)=\frac uh\,\lambda([h]P_0).$$

These are the manuscript's full-log ratios: the ratio of two full logarithms of multiples of
$P_0$ in the formal group is a rational number, the ratio of the indices.

**Proof sketch.** Put $H=[h]P_0$ and $U=[u]P_0$. Since $P_0$ has infinite order, $H\ne O$. As
$p$ is odd and unramified, the isometry range of the logarithm is all of $E_1(K_{\mathfrak p})$,
so $\lambda$ is injective on it and $\lambda(H)\ne0$. Both $[u]H$ and $[h]U$ equal $[uh]P_0$ and lie in the subgroup
$E_1(K_{\mathfrak p})$, and $\lambda$ is a homomorphism, so
$u\lambda(H)=\lambda([u]H)=\lambda([h]U)=h\lambda(U)$.

## Depends on

- [The point $P_0$](../../model/field/generator-point.md)
- [The formal logarithm](formal-logarithm.md)
- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](primes-above-p.md)
- [Mordell–Weil for the generator curve](../../main/mordell-weil.md)

## Proof depends on

- [The generator certificate](../../model/generator.md)
- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](formal-group.md)
- [The isometry range of the formal logarithm](logarithm-isometry.md)

## Sources

- [Local congruence](../../../sources/multiplication-locators.md#local-congruence)
- [Local conventions](../../../sources/multiplication-locators.md#local-conventions)
