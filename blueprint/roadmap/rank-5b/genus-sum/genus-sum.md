---
article_id: af_f842c459324b1507e04f1551
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank5b.T5b, ZInQ.RouteK.Rank5b.Admissible5bNat, ZInQ.RouteK.Rank5b.dProd, ZInQ.RouteK.Rank5b.Sec3.genusSum5b, ZInQ.RouteK.Rank5b.Sec3.Admissible5b
---

# The genus sum $T_{5b}$

Let $a,y,z$ be bits on a finite set $V$. A set $B\subseteq V$ has *class* $1$, $5$, $7$ or $3$
according as $(y(B),z(B))$ is $(0,0)$, $(0,1)$, $(1,0)$ or $(1,1)$. The *genus sum of row 5b* of the
bits is
$$T_{5b}=\sum_\pi\prod_{B\in\pi}g(B),$$
the sum over the set partitions $\pi$ of $V$ (into nonempty blocks) with exactly one block of class
$7$, exactly one block of class $3$ and no block of class $5$, so that all other blocks have class
$1$.

For a natural number $n$ with set of primes $P$ and $B\subseteq P$ put $d_B=\prod_{p\in B}p$. The
*genus sum* of $n$ is
$$T_{5b}(n)=\sum_\pi\prod_{B\in\pi}g_n(B),$$
the sum over the set partitions $\pi$ of $P$ with exactly one block with $d_B\equiv7\pmod8$, exactly
one block with $d_B\equiv3\pmod8$, and every block with $d_B\equiv7$, $3$ or $1\pmod8$. In Smith's
notation, $T_{5b}(n)=\sum_{d_0\equiv7,\,d_1\equiv3\,(8)}g_n(d_0)g_n(d_1)\mathcal L_1(n/d_0d_1)$, where
$g_n(d_0)$ is $g_n(B)$ for the block $B$ with $d_B=d_0$ and $\mathcal L_1(m)$ is the sum of
$\prod g_n$ over the partitions of the primes of $m$ into blocks $\equiv1\pmod8$.

## Depends on

- [Rédei's $g$ from the bits](redei-g.md)

## Sources

- [Notation](../../../sources/rank-5b-locators.md#notation)
- [Smith](../../../sources/rank-5b-locators.md#smith)
