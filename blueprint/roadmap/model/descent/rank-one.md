---
article_id: af_d5ceda39108993ca5f43dce3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.exists_generator_E, ZInQ.exists_generator_C
---

# $E(K_0)$ has rank one

Assume that $E(K_0)$ is finitely generated (the Mordell-Weil hypothesis). Then there is a
point $S\in C(K_0)$ of infinite order such that every $P\in C(K_0)$ is uniquely
$P=[m]S+T$ with $m\in\mathbb Z$ and $T\in C(K_0)[2]$:
$$C(K_0)=\mathbb ZS\oplus C(K_0)[2]\cong\mathbb Z\times(\mathbb Z/2\mathbb Z)^2 .$$
The same holds for $E(K_0)$ with $\theta^{-1}(S)$ and $E(K_0)[2]$.

**Proof sketch.** $C(K_0)\cong E(K_0)$ via $\theta$, so $C(K_0)$ is finitely generated with torsion
subgroup $C(K_0)[2]\cong(\mathbb Z/2\mathbb Z)^2$ and $[C(K_0):2C(K_0)]=8$. By the structure theorem,
$C(K_0)\cong\mathbb Z^r\oplus(\mathbb Z/2\mathbb Z)^2$, whose quotient by twice itself has order
$2^{r+2}$; so $r=1$. Concretely, $C(K_0)/C(K_0)[2]$ is torsion-free, finitely generated and of
rank one, hence infinite cyclic; any $S$ mapping to a generator works, and the sum is direct
because $\mathbb ZS$ is torsion-free.

## Depends on

- [Mordell–Weil for the generator curve](../../main/mordell-weil.md)
- [The change of variables to $C$](coordinate-change.md)

## Proof depends on

- [The index $[E(K_0):2E(K_0)]=8$](descent-index.md)
- [The torsion of $E(K_0)$ is the full two-torsion](torsion.md)

## Sources

- [Rank and odd index](../../../sources/model-locators.md#rank-and-odd-index)
