---
article_id: af_ce3c30d97ae1262bb24c3776
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.delta_eq_one_iff, ZInQ.RouteK.Rank.deltaHom_ker_eq, ZInQ.RouteK.Rank.not_isSquare_two_rat, ZInQ.RouteK.Rank.rat_two_ne_zero, ZInQ.RouteK.Rank.rat_d_ne_zero
---

# The kernel of the descent map over the rationals

Let $d$ be a positive integer. For $P\in C_d(\mathbb Q)$,
$$\delta_d(P)=1\iff P=2Q\text{ for some }Q\in C_d(\mathbb Q).$$
So the kernel of the homomorphism $\delta_d$ on $C_d(\mathbb Q)$ is $2C_d(\mathbb Q)$. Along the
way: $2\ne0$ and $d\ne0$ in $\mathbb Q$, and $2$ is not a square in $\mathbb Q$.

**Proof sketch.** (⇐) is the last part of the homomorphism theorem. (⇒) Take $P=O$ to $Q=O$. At
$(0,0)$ the first coordinate is the class of $-d^2<0$, not a square. At $(d,0)$ the second is the
class of $2d^2$, not a square since $2$ is not a rational square (a squarefree integer that is a
rational square is $1$). At any other point $(x,y)$, $x$ and $x-d$ are squares, $x=r_1^2$ and
$x-d=r_2^2$. Then $x+d\ne0$, since otherwise $x=-d<0$. Also $r_1r_2\ne0$, as $x(x-d)\ne0$. Put
$r_3=y/(r_1r_2)$; then $r_3^2=y^2/(x(x-d))=x+d$, and the halving lemma gives $Q$.

## Depends on

- [The complete 2-descent map of a congruent number curve](descent-map.md)
- [The complete 2-descent map is a homomorphism](descent-map-homomorphism.md)

## Proof depends on

- [The halving lemma](halving.md)
- [The certified rank hypothesis from its Selmer form](../../selmer/certified-rank-of-sel.md)

## Sources

- [The complete 2-descent map](../../../sources/rank-locators.md#the-complete-2-descent-map)
- [Halving](../../../sources/rank-locators.md#halving)
