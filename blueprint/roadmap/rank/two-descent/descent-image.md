---
article_id: af_cf69d1d1ebebd169a1fd75c4
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.selRep_mem_sel2, ZInQ.RouteK.Rank.selRep, ZInQ.RouteK.Rank.loc_selRep, ZInQ.RouteK.Rank.selRep_eq_iff, ZInQ.RouteK.Rank.loc_map, ZInQ.RouteK.Rank.loc_cast_of_loc_rat
---

# The image of the descent map lies in the 2-Selmer group

Let $d$ be a positive integer. For $P\in C_d(\mathbb Q)$ with $\delta_d(P)=(\alpha,\beta)$, let
$s(P)=(r(\alpha),r(\beta))\in\mathbb Z^2$ be the pair of squarefree representatives. Then the
x-form of the covering $D_{s(P)}$ holds over $\mathbb Q$, and $s(P)\in\mathrm{Sel}_2(C_d)$. For
$P,Q\in C_d(\mathbb Q)$ (and any natural number $d$), $s(P)=s(Q)$ if and only if
$\delta_d(P)=\delta_d(Q)$.

Along the way: if $f:K\to L$ is a homomorphism of fields and the x-form of $D_{a,b}$ for $d$ holds
over $K$, then the x-form of $D_{f(a),f(b)}$ for $f(d)$ holds over $L$. In particular, for a natural
number $d$ and integers $a,b$, the x-form of $D_{a,b}$ over $\mathbb Q$ gives the x-form of $D_{a,b}$
over every field of characteristic zero.

**Proof sketch.** By the comparison with the Kummer map of the coverings,
$r(\alpha)\equiv k_1(P)$ and $r(\beta)\equiv k_2(P)$, and $k_1(P)$, $k_2(P)$ are nonzero. So by the
Kummer-map lemma over $\mathbb Q$ the x-form of $D_{s(P)}$ holds over $\mathbb Q$. A field
homomorphism sends squares to squares, so the x-form is carried to $\mathbb R$ and to every
$\mathbb Q_p$. Both representatives are squarefree, so $s(P)\in\mathrm{Sel}_2(C_d)$. The last claim
holds because $r$ is injective.

## Depends on

- [The complete 2-descent map of a congruent number curve](descent-map.md)
- [Squarefree representatives of rational square classes](squarefree-representatives.md)
- [The 2-Selmer group of a congruent number curve](../../selmer/selmer-group.md)
- [The 2-coverings of a congruent number curve](../../selmer/coverings.md)

## Proof depends on

- [The descent map is the Kummer map of the coverings](descent-map-kummer.md)
- [Coverings and the Kummer map](../../selmer/kummer-map.md)
- [The kernel of the descent map over the rationals](descent-kernel.md)

## Sources

- [RK9](../../../sources/rank-locators.md#rk9)
- [The Kummer map](../../../sources/selmer-locators.md#the-kummer-map)
- [The Selmer group](../../../sources/selmer-locators.md#the-selmer-group)
