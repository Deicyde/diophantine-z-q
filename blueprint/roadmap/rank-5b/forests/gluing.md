---
article_id: af_ed20659bce59e10b32da0289
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.prod_sum_allF, ZInQ.RouteK.Rank5b.Sec3.restrict, ZInQ.RouteK.Rank5b.Sec3.iterate_agree, ZInQ.RouteK.Rank5b.Sec3.root_agree, ZInQ.RouteK.Rank5b.Sec3.restrict_mem_allF, ZInQ.RouteK.Rank5b.Sec3.ofPartFun, ZInQ.RouteK.Rank5b.Sec3.part_ofPartFun, ZInQ.RouteK.Rank5b.Sec3.parts_eq_image_part, ZInQ.RouteK.Rank5b.Sec3.finpartition_ext_part, ZInQ.RouteK.Rank5b.Sec3.mem_part_univ, ZInQ.RouteK.Rank5b.Sec3.part_mem_univ, ZInQ.RouteK.Rank5b.Sec3.part_eq_part_of_mem
---

# Gluing forests along a set partition

Let $\pi$ be a set partition of a finite set $V$, and write $\pi(i)$ for the block containing $i$.
For a map $f:V\to V$ and $B\subseteq V$ let $f|_B$ be the map equal to $f$ on $B$ and to the
identity off $B$. For each block $B$ and each map $g$ let $h_B(g)\in\mathbb F_2$. Then
$$\prod_{B\in\pi}\ \sum_{g}h_B(g)=\sum_f\ \prod_{B\in\pi}h_B(f|_B),$$
where in the factor of $B$, $g$ runs over the forests on $B$, and $f$ runs over the forests on $V$
with $f(i)\in\pi(i)$ for every $i$, that is, those that map every block into itself.

Along the way:

1. if a map $g$ sends $B$ into $B$ and $f$ agrees with $g$ on $B$, then on $B$ the iterates of $f$
   agree with those of $g$ and stay in $B$; in particular $f$ and $g$ have the same roots at the
   points of $B$, and these roots lie in $B$;
2. if $f$ is a forest on $V$ that maps $B$ into itself, then $f|_B$ is a forest on $B$;
3. every point lies in its block, every $\pi(i)$ is a block, the blocks are exactly the sets
   $\pi(i)$, and $j\in\pi(i)$ implies $\pi(j)=\pi(i)$; a set partition is determined by its blocks
   $\pi(i)$, $i\in V$;
4. a function $b$ from $V$ to the subsets of $V$ with $i\in b(i)$ for all $i$, and $b(j)=b(i)$
   whenever $j\in b(i)$, is the block function of a set partition, the one whose blocks are the sets
   $b(i)$.

**Proof sketch.** Expanding the product of sums gives a sum over the families $(g_B)_{B\in\pi}$ of
forests on the blocks. Glue such a family into the map $f$ with $f(j)=g_{\pi(j)}(j)$. It maps each
block into itself, and it is acyclic: on a block $B$ it agrees with $g_B$, which maps $B$ into
itself, so by (1) the root of a point of $B$ is its root under $g_B$, a point of $B$ fixed by $g_B$
and hence by $f$. Conversely, a forest $f$ on $V$ that maps each block into itself has the
restrictions $f|_B$, which are forests on the blocks by (2). Gluing the restrictions returns $f$,
and restricting a glued family returns the family, since each $g_B$ is the identity off $B$. This
bijection matches the terms.

## Depends on

- [Forests on a finite set](forests.md)

## Sources

- [Propositions 3.3 and 3.4](../../../sources/rank-5b-locators.md#propositions-33-and-34)
- [Proposition 3.5](../../../sources/rank-5b-locators.md#proposition-35)
- [Theorem 3.6](../../../sources/rank-5b-locators.md#theorem-36)
