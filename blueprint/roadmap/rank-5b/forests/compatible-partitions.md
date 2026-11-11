---
article_id: af_2c86e0e0fe0bfd67cf558526
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.card_setA, ZInQ.RouteK.Rank5b.Sec3.Resp, ZInQ.RouteK.Rank5b.Sec3.part_iterate, ZInQ.RouteK.Rank5b.Sec3.part_root, ZInQ.RouteK.Rank5b.Sec3.mem_part_iff_root, ZInQ.RouteK.Rank5b.Sec3.root_mem_rootsOf, ZInQ.RouteK.Rank5b.Sec3.root_eq_self, ZInQ.RouteK.Rank5b.Sec3.setA, ZInQ.RouteK.Rank5b.Sec3.bS
---

# Set partitions compatible with a forest

Let $f$ be a forest on a finite set $V$, with root map $r$ and set of roots $R$ (its fixed points);
every root $r(i)$ lies in $R$, and each element of $R$ is its own root. A set partition $\pi$ of
$V$ is *compatible* with $f$ if $f(i)$ lies in the block $\pi(i)$ of $i$ for every $i$. In a
compatible partition, $\pi(f^k(i))=\pi(i)$ for all $k$, so $\pi(r(i))=\pi(i)$: a point lies in a
block if and only if its root does.

Let $\rho_7\ne\rho_3$ be roots of $f$. Then the set partitions $\pi$ compatible with $f$ such that
$\rho_7$ is the only root in its block, $\rho_3$ is the only root in its block, and the block of
every other root contains exactly two roots, are as many as the pairings of
$R\setminus\{\rho_7,\rho_3\}$.

**Proof sketch.** Extend a pairing $s$ of $R\setminus\{\rho_7,\rho_3\}$ by the identity and put
$b_s(i)=\{j\in V:r(j)=r(i)\text{ or }r(j)=s(r(i))\}$. Then $i\in b_s(i)$, and $j\in b_s(i)$ implies
$b_s(j)=b_s(i)$ because $s$ is an involution, so $b_s$ is the block function of a set partition
$\pi_s$. It is compatible with $f$, since $r(f(i))=r(i)$. The roots in the block of $\rho_7$ are
just $\rho_7$, since $s$ fixes $\rho_7$, and likewise for $\rho_3$; the roots in the block of any
other root $\rho$ are $\rho$ and $s(\rho)\ne\rho$. The map $s\mapsto\pi_s$ is injective, since
$s(\rho)$ is the root other than $\rho$ in the block of $\rho$. It is onto: given such a partition
$\pi$, let $s(\rho)$ be the other root in the block of $\rho$, for $\rho\in R\setminus\{\rho_7,
\rho_3\}$. Then $s(\rho)\notin\{\rho_7,\rho_3\}$, as otherwise $\rho$ would be a second root in
their block, and $s(s(\rho))=\rho$, so $s$ is a pairing. Finally $\pi=\pi_s$, because the block of
$i$ in either partition consists of the points whose root lies in the block of $r(i)$, and the
roots in that block are $r(i)$ and $s(r(i))$; a set partition is determined by its blocks.

## Depends on

- [Forests on a finite set](forests.md)
- [Pairings are odd in number exactly on sets of even size](pairings.md)

## Proof depends on

- [Gluing forests along a set partition](gluing.md)

## Sources

- [Theorem 3.6](../../../sources/rank-5b-locators.md#theorem-36)
- [Row 5b of Smith's table](../../../sources/rank-5b-locators.md#row-5b-of-smiths-table)
