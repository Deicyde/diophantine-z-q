---
article_id: af_ddcc6f0d8376316caa27b583
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.genusSum5b_eq_marked, ZInQ.RouteK.Rank5b.Sec3.markW, ZInQ.RouteK.Rank5b.Sec3.w7_eq_zero, ZInQ.RouteK.Rank5b.Sec3.w3_eq_zero, ZInQ.RouteK.Rank5b.Sec3.w1_eq_zero, ZInQ.RouteK.Rank5b.Sec3.classes_of_markW_ne_zero, ZInQ.RouteK.Rank5b.Sec3.markW', ZInQ.RouteK.Rank5b.Sec3.class73_eq_marked
---

# Partition sums with marked blocks

Let $a,y,z$ be bits on a finite set $V$, and let $w_7,w_3,w_1$ be the block weights: $w_c(B)$ is
$g(B)$ if $B$ has class $c$ and $0$ otherwise.

1. (The genus sum.) For blocks $B_7\ne B_3$ let $m_{B_7,B_3}$ be $w_7$ on $B_7$, $w_3$ on $B_3$ and
   $w_1$ on every other set. Then
   $$T_{5b}=\sum_\pi\ \sum_{B_7\in\pi}\ \sum_{B_3\in\pi,\,B_3\ne B_7}\ \prod_{B\in\pi}m_{B_7,B_3}(B),$$
   the outer sum over all set partitions $\pi$ of $V$. If a product
   $\prod_{B\in\pi}m_{B_7,B_3}(B)$ is nonzero, then $B_7$ has class $7$, $B_3$ has class $3$ and every
   other block of $\pi$ has class $1$.
2. (One block of class $7$, the others of class $3$.) For a block $B_7$ let $m'_{B_7}$ be $w_7$ on
   $B_7$ and $w_3$ on every other set. For every set partition $\pi$ of $V$, the sum
   $\sum_{B_7\in\pi}\prod_{B\in\pi}m'_{B_7}(B)$ is $\prod_{B\in\pi}g(B)$ if $\pi$ has exactly one block of
   class $7$ and all other blocks of class $3$, and $0$ otherwise.

**Proof sketch.** A factor $w_c(B)$ vanishes unless $B$ has class $c$. So a nonzero marked product
forces the classes of the marked blocks and of the others. (1) In a partition counted by $T_{5b}$
the blocks of classes $7$ and $3$ are unique, so its marked sum has exactly one nonzero term,
$\prod_Bg(B)$; for any other partition every marked product vanishes. (2) If $\pi$ has exactly one
block of class $7$ and the others of class $3$, the only marked choice with nonzero product is that
block, and the product is $\prod_Bg(B)$. Otherwise a nonzero marked product would make $B_7$ a block
of class $7$ and all other blocks of class $3$, which is excluded.

## Depends on

- [The genus sum $T_{5b}$](genus-sum.md)
- [Rédei's $g$ from the bits](redei-g.md)
- [Block weights as forest sums](block-weights.md)

## Sources

- [Theorem 3.6](../../../sources/rank-5b-locators.md#theorem-36)
- [Propositions 3.3 and 3.4](../../../sources/rank-5b-locators.md#propositions-33-and-34)
