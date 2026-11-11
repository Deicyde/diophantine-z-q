---
article_id: af_ae559fdab397e6c566581d45
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.card_setAgen, ZInQ.RouteK.Rank5b.Sec3.setAgen, ZInQ.RouteK.Rank5b.Sec3.card_setAgen_roots, ZInQ.RouteK.Rank5b.Sec3.resp_blocks_iff, ZInQ.RouteK.Rank5b.Sec3.card_uniform_eq
---

# Compatible partitions with one or two roots per block

Let $f$ be a forest on a finite set $V$ with root set $R$, and let $E\subseteq R$. The set
partitions compatible with $f$ in which every root in $E$ is the only root of its block and every
block containing a root outside $E$ contains exactly two roots are as many as the fixed-point-free
involutions of $R\setminus E$. For $E=R$ there is exactly one.

For $k=1$ or $2$, a set partition compatible with $f$ has exactly $k$ roots in every block if and
only if it is one of the partitions of the count with $E=R$, respectively $E=\emptyset$. So the
number of compatible partitions with exactly $k$ roots in every block is the number for $E=R$,
respectively $E=\emptyset$.

**Proof sketch.** A fixed-point-free involution $s$ of $R\setminus E$, extended by the identity on
$E$, gives the partition whose block at a root $\rho$ is the set of points whose root is $\rho$ or
$s(\rho)$; this is a bijection onto the partitions described. For $E=R$ the only involution of the
empty set gives the partition into the trees of $f$. Since every block of a compatible partition
contains a root, "every block has exactly $k$ roots" is the condition of the count with $E=R$ for
$k=1$ and with $E=\emptyset$ for $k=2$.

## Depends on

- [Forests on a finite set](../forests/forests.md)
- [Set partitions compatible with a forest](../forests/compatible-partitions.md)
- [Pairings are odd in number exactly on sets of even size](../forests/pairings.md)

## Proof depends on

- [Gluing forests along a set partition](../forests/gluing.md)

## Sources

- [Propositions 3.3 and 3.4](../../../sources/rank-5b-locators.md#propositions-33-and-34)
