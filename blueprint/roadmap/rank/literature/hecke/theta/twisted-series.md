---
article_id: af_942eca1d1fd14af5abf9e6a7
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.twistedL, ZInQ.Contrib.HeckeFE.blockEquiv, ZInQ.Contrib.HeckeFE.blockEquiv_apply, ZInQ.Contrib.HeckeFE.gz_block, ZInQ.Contrib.HeckeFE.gq_block, ZInQ.Contrib.HeckeFE.summable_twisted, ZInQ.Contrib.HeckeFE.twistedL_eq, ZInQ.Contrib.HeckeFE.twistedL_continuation, ZInQ.Contrib.HeckeFE.LSeries_eq_twistedL
---

# Periodic twists of the lattice series and their continuation

Let $M\ge1$ be a natural number and $c:(\mathbb Z/M)^2\to\mathbb C$ any function. Write a point
$\alpha=(\alpha_1,\alpha_2)\in\mathbb Z^2$ also as the Gaussian integer $\alpha_1+\alpha_2i$, with
norm $N(\alpha)=\alpha_1^2+\alpha_2^2$, and $c(\alpha)$ for $c(\alpha_1\bmod M,\alpha_2\bmod M)$. The
*twisted lattice series* is
$$T_c(s)=\sum_{\alpha\in\mathbb Z^2}\frac{c(\alpha)\,\alpha}{N(\alpha)^s},$$
read as $0$ where the family is not summable; the term $\alpha=0$ is $0$. In the notation of
[the lattice Dirichlet series](lattice-series.md), $\alpha=z_{0,0}(\alpha)$ and
$N(\alpha)=N_{0,0}(\alpha)$. Let $L_{a,b}$ be the lattice Dirichlet series and $A_n$ the
[set of Gaussian integers of norm $n$](../gaussian/norm-fibres.md).

1. The map $\{0,\dots,M-1\}^2\times\mathbb Z^2\to\mathbb Z^2$, $(j,q)\mapsto(q_1M+j_1,q_2M+j_2)$, is a
   bijection; for $\alpha=qM+j$, $\alpha=M\,z_{j_1/M,j_2/M}(q)$ and
   $N(\alpha)=M^2N_{j_1/M,j_2/M}(q)$.
2. For $\operatorname{Re}s>3/2$ the family defining $T_c(s)$ is absolutely summable, and
   $$T_c(s)=\sum_{j\in\{0,\dots,M-1\}^2}c(j)\,\frac{M}{(M^2)^s}\,L_{j_1/M,\,j_2/M}(s).$$
3. (Hecke's continuation for periodic twists.) There is an entire function $F$ with $F(s)=T_c(s)$
   for every $s$ with $\operatorname{Re}s>3/2$.
4. (Grouping by the norm.) Let $a:\mathbb N\to\mathbb C$ satisfy
   $a(n)=\sum_{\alpha\in A_n}c(\alpha)\,\alpha$ for every $n\ge1$. Then for every $s$ with
   $\operatorname{Re}s>3/2$, the L-series $\sum_{n\ge1}a(n)n^{-s}$ (read as $0$ where the family is
   not summable) equals $T_c(s)$.

**Proof sketch.** (1) Division with remainder by $M$ in each coordinate.

(2) $|c|$ is bounded by $\sum_x|c(x)|$, so absolute summability follows from that of
$z_{0,0}/N_{0,0}^s$ ([the lattice Dirichlet series](lattice-series.md) (4)). Reindex the sum by (1)
and sum over $j$ first (a finite sum); $c(qM+j)=c(j)$, and since $M^2$ and $N_{j/M}(q)$ are real and
nonnegative, $(M^2N_{j/M}(q))^s=(M^2)^sN_{j/M}(q)^s$, which gives the factor $M(M^2)^{-s}$.

(3) Each $L_{j_1/M,j_2/M}$ agrees on $\operatorname{Re}s>3/2$ with an entire function
([the lattice Dirichlet series](lattice-series.md) (5)), and $s\mapsto M(M^2)^{-s}$ is entire. The
finite combination in (2) of these entire functions is entire and agrees with $T_c$ there.

(4) The family of (2) is summable; group it by the value $n=N(\alpha)$. The group $n=0$ is
$\{\alpha=0\}$, whose term is $0$. For $n\ge1$ the group is $A_n$, on which $N(\alpha)^s=n^s$, so
its sum is $a(n)n^{-s}$.

## Depends on

- [The lattice Dirichlet series and its entire continuation](lattice-series.md)
- [Gaussian integers as pairs, norms and units](../gaussian/norm-fibres.md)

## Sources

- [Theta series and the method of Hecke](../../../../../sources/hecke-locators.md#theta-series-and-the-method-of-hecke)
