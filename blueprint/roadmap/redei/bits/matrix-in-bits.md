---
article_id: af_2dd1949250529505605e9374
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.redeiB_sum_entry, ZInQ.RouteK.Redei.redeiB_entry_eq_lapl
---

# The Rédei matrix of $\mathbb Q(\sqrt{-d_B})$ in the bits

Let $d$ be odd, $B$ a set of primes of $d$, $R$ the Rédei matrix of $d_B$, and $L_B$ the Laplacian
on $B$ of the bits $a_{qp}=[p/q]$ of $d$. For $q\in B$ and every function $F$ from the natural
numbers to $\mathbb F_2$,
$$\sum_{p\in T_{d_B}}R_{qp}F(p)=\sum_{p\in B}(L_B)_{qp}F(p)+\begin{cases}0,&d_B\equiv3\pmod4,\\
z_qF(2),&\text{otherwise.}\end{cases}$$
More precisely, for $q\in B$ and every prime $p$ of $d$, the entry given by the formula of the
Rédei matrix of $d_B$, namely $[p/q]$ for $p\ne q$ and $[(d_B/q)/q]$ for $p=q$, equals
$(L_B)_{qp}$.

**Proof sketch.** The off-diagonal entries are $[p/q]=a_{qp}=(L_B)_{qp}$. On the diagonal,
$d_B/q=\prod_{k\in B,\,k\ne q}k$, and the other primes of $B$ are prime to $q$, so by the
multiplicativity of the residue bit $[(d_B/q)/q]=\sum_{k\in B,\,k\ne q}[k/q]=(L_B)_{qq}$. The set
$T_{d_B}$ is $B$ if $d_B\equiv3\pmod4$ and $B\cup\{2\}$ otherwise, with $2\notin B$; the column at
$2$ has entries $[2/q]=z_q$.

## Depends on

- [The Rédei matrix](../redei-matrix.md)
- [The primes of $d_B$](primes-of-d-b.md)
- [The Laplacian of a family of bits](../../rank-5b/forests/laplacian.md)
- [Smith's matrices $L$, $M_1$ and $M_{5b}$](../../rank-5b/smith-matrices.md)

## Proof depends on

- [Quadratic reciprocity in residue bits](../../route-k/reciprocity-bits.md)

## Sources

- [Step 8: the bridge](../../../sources/redei-locators.md#step-8-the-bridge)
