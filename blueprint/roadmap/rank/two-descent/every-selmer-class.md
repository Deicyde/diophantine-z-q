---
article_id: af_935f4af5ebe1b4d3a0dffb79
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.loc_of_mem_sel2_of_infinite_order, ZInQ.RouteK.Rank.card_quotient_two_eq_ncard_range_selRep, ZInQ.RouteK.Rank.repPair, ZInQ.RouteK.Rank.repPair_injective
---

# Positive rank and a Selmer group of order eight give every Selmer class (RK9)

Let $d$ be a positive integer. Suppose that $C_d(\mathbb Q)$ is finitely generated, that it has a
point of infinite order, and that $\mathrm{Sel}_2(C_d)$ has exactly $8$ elements. Then for every
$(a,b)\in\mathrm{Sel}_2(C_d)$ the x-form of the covering $D_{a,b}$ holds over $\mathbb Q$.

Along the way: the pair of squarefree representatives
$(\alpha,\beta)\mapsto(r(\alpha),r(\beta))$ is injective on $(\mathbb Q^\times/\mathbb Q^{\times2})^2$,
and $C_d(\mathbb Q)/2C_d(\mathbb Q)$ has as many elements as the set of pairs $s(P)$,
$P\in C_d(\mathbb Q)$.

**Proof sketch.** Since the kernel of $\delta_d$ is $2C_d(\mathbb Q)$,
$C_d(\mathbb Q)/2C_d(\mathbb Q)$ is in bijection with the image of $\delta_d$, and through the
injective pair of representatives with the set $S=\{s(P)\}$. The image theorem gives
$S\subseteq\mathrm{Sel}_2(C_d)$. The Selmer group has $8$ elements, so $S$ is finite, and it is
nonempty since it contains $s(O)$; hence $C_d(\mathbb Q)/2C_d(\mathbb Q)$ is finite. Over
$\mathbb Q$ the $2$-torsion of $C_d$ has exactly $4$ elements, so the counting theorem gives
$\#S\ge8=\#\mathrm{Sel}_2(C_d)$, and $S=\mathrm{Sel}_2(C_d)$. Every element of $S$ is some $s(P)$,
and the x-form of its covering holds over $\mathbb Q$.

## Depends on

- [The 2-Selmer group of a congruent number curve](../../selmer/selmer-group.md)
- [The 2-coverings of a congruent number curve](../../selmer/coverings.md)
- [Squarefree representatives of rational square classes](squarefree-representatives.md)
- [The image of the descent map lies in the 2-Selmer group](descent-image.md)

## Proof depends on

- [The kernel of the descent map over the rationals](descent-kernel.md)
- [The two-torsion of a congruent number curve](two-torsion.md)
- [Counting $A/2A$](counting.md)
- [The complete 2-descent map is a homomorphism](descent-map-homomorphism.md)

## Sources

- [RK9](../../../sources/rank-locators.md#rk9)
- [The positive-rank form](../../../sources/rank-locators.md#the-positive-rank-form)
