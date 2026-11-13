---
article_id: af_c22b2cde441d558c7563f946
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.T5b_eq_genusSum5b, ZInQ.RouteK.Rank5b.yBit_eq_lam8, ZInQ.RouteK.Rank5b.zBit_eq_mu8, ZInQ.RouteK.Rank5b.dProd_mem_oddClasses, ZInQ.RouteK.Rank5b.sum_yBit_eq, ZInQ.RouteK.Rank5b.sum_zBit_eq, ZInQ.RouteK.Rank5b.natMod8_eq_iff_cast, ZInQ.RouteK.Rank5b.dProd_class_iff, ZInQ.RouteK.Rank5b.admissible5bNat_iff
---

# The genus sum of an odd number from its bits

Let $n$ be odd with set of primes $P$ and bits $a_{pq}$, $y_p$, $z_p$, and let $B\subseteq P$. Then
$d_B=\prod_{p\in B}p$ is odd, $y_p=\lambda(p)$ and $z_p=\mu(p)$ for every $p\in P$, and
$$y(B)=\lambda(d_B),\qquad z(B)=\mu(d_B),$$
where $\lambda(c)=[c\equiv3\pmod4]$ and $\mu(c)=[c\equiv3,5\pmod8]$. Consequently $d_B\equiv7\pmod8$ if
and only if $B$ has class $7$, $d_B\equiv3\pmod8$ if and only if $B$ has class $3$, and
$d_B\equiv7,3$ or $1\pmod8$ if and only if $B$ does not have class $5$. So a set partition of $P$ is
counted by $T_{5b}(n)$ if and only if it is counted by the genus sum $T_{5b}$ of the bits of $n$, and
$$T_{5b}(n)=T_{5b}\quad\text{for the bits }a_{pq},\,y_p,\,z_p\text{ of }n.$$

**Proof sketch.** For a prime $p\mid n$, $y_p=(-1/p)_+=\lambda(p)$ and $z_p=(2/p)_+=\mu(p)$. The maps
$\lambda$ and $\mu$ are additive on the odd classes modulo $8$, and $d_B$ is a product of odd primes,
so $y(B)=\lambda(d_B)$ and $z(B)=\mu(d_B)$. An odd class modulo $8$ is determined by its values of
$\lambda$ and $\mu$, which gives the three equivalences, checked on the four odd classes. So the
conditions defining $T_{5b}(n)$ and $T_{5b}$ select the same set partitions, and the products
$\prod_Bg_n(B)$ are the same by definition.

## Depends on

- [The genus sum $T_{5b}$](genus-sum.md)
- [Configurations](../../route-k/configuration.md)
- [Smith's matrices $L$, $M_1$ and $M_{5b}$](../smith-matrices.md)

## Sources

- [Notation](../../../sources/rank-5b-locators.md#notation)
