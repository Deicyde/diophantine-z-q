---
article_id: af_d2ff03c36320c9d4adfb775e
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.redeiG, ZInQ.RouteK.Rank5b.Sec3.kappa, ZInQ.RouteK.Rank5b.Sec3.Recip, ZInQ.RouteK.Rank5b.gBit
---

# Rédei's $g$ from the bits

Let $V$ be a finite set with bits $a_{ij}\in\mathbb F_2$ ($i,j\in V$) and $y_i,z_i\in\mathbb F_2$
($i\in V$). For $S\subseteq V$ write $y(S)=\sum_{i\in S}y_i$ and $z(S)=\sum_{i\in S}z_i$. The bits
satisfy *reciprocity* if $a_{ij}+a_{ji}=y_iy_j$ for all $i\ne j$ in $V$.

For $B\subseteq V$ let $L_B$ be the Laplacian of the bits $a$ on $B$, and for $\rho\in V$ put
$$\kappa_\rho(B)=\det L_B[B\setminus\{\rho\},\,B\setminus\{\rho\}],$$
the principal minor of $L_B$ on the rows and columns of $B\setminus\{\rho\}$; for $B=\{\rho\}$ it is
the empty determinant $1$. *Rédei's $g$* of $B$ is
$$g(B)=\begin{cases}\sum_{\rho\in B}y_\rho\,\kappa_\rho(B)&\text{if }y(B)=1,\\
\sum_{\rho\in B}z_\rho\,\kappa_\rho(B)&\text{if }y(B)=0.\end{cases}$$

For a natural number $n$ with set of primes $P$ and $B\subseteq P$, $g_n(B)$ is $g(B)$ for the bits
of the primes of $n$ of Smith's matrices: $a_{pq}=(q/p)_+$, $y_p=(-1/p)_+$ and $z_p=(2/p)_+$.

The definition does not assume reciprocity. Under reciprocity and $y(B)=1$ the cofactors
$\kappa_\rho(B)$, $\rho\in B$, are all equal (Lemma 2.2), and since $\sum_{\rho\in B}y_\rho=1$ the first
case is their common value $\kappa(B)$; this is Rédei's form $g(B)=\kappa(B)$. For odd squarefree $n$
and a nonempty $B$ with $d_B=\prod_{p\in B}p\equiv7,3$ or $1\pmod8$, [Rédei's
formula](../../redei/redei-formula.md) identifies $g_n(B)$ with the parity of the order of the
subgroup of squares $2\mathrm{Cl}$ of the class group of $\mathbb Q(\sqrt{-d_B})$.

## Depends on

- [Smith's matrices $L$, $M_1$ and $M_{5b}$](../smith-matrices.md)
- [The Laplacian of a family of bits](../forests/laplacian.md)

## Sources

- [Proposition 2.3](../../../sources/rank-5b-locators.md#proposition-23)
