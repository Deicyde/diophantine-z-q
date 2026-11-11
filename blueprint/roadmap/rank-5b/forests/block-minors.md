---
article_id: af_1ac0d96a8c129fe192a83fb5
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.pmin_fromBlocks_anti, ZInQ.RouteK.Rank5b.Sec3.glue, ZInQ.RouteK.Rank5b.Sec3.pmin_add_diagonal
---

# Minors of anti-diagonal block matrices and of diagonal shifts

Minors over $\mathbb F_2$ are the permanent minors $\operatorname{per}M[R,C]$, sums over the
bijections $R\to C$.

1. (Anti-diagonal blocks.) Let $M,N$ be $V\times V$ matrices over $\mathbb F_2$ and $A,C\subseteq V$.
   On the rows and columns $A\sqcup C$ of $V\sqcup V$,
   $$\operatorname{per}\begin{pmatrix}0&M\\N&0\end{pmatrix}[A\sqcup C,A\sqcup C]
   =\operatorname{per}M[A,C]\cdot\operatorname{per}N[C,A].$$
2. (Diagonal shift.) Let $Q$ be a square matrix over $\mathbb F_2$ indexed by a finite set $X$, and
   $e\in\mathbb F_2^X$ with diagonal matrix $D_e$. Then
   $$\operatorname{per}(Q+D_e)[X,X]=\sum_{S\subseteq X}e^S\operatorname{per}Q[X\setminus S,X\setminus S],
   \qquad e^S=\prod_{x\in S}e_x.$$

**Proof sketch.** (1) A pair of bijections $\nu:A\to C$ and $\tau:C\to A$ glues to the bijection of
$A\sqcup C$ that sends $a$ in the first copy to $\nu(a)$ in the second and $c$ in the second copy to
$\tau(c)$ in the first, and its product is the product of the two. Every bijection of $A\sqcup C$
with a nonzero product sends each copy into the other, since the diagonal blocks vanish, and so
arises from exactly one such pair. (2) Write each entry as $(D_e)_{x\sigma(x)}+Q_{x\sigma(x)}$ and expand
$\prod_x(Q+D_e)_{x\sigma(x)}$ over the sets $S$ of points where the diagonal term is taken. The
term vanishes unless $\sigma$ fixes $S$ pointwise, and then it is
$e^S\prod_{x\notin S}Q_{x\sigma(x)}$. Exchange the sums: the bijections of $X$ that fix $S$
pointwise are the bijections of $X\setminus S$.

## Depends on

- [Minors over $\mathbb F_2$ as permanents](permanent-minors.md)

## Sources

- [Propositions 3.3 and 3.4](../../../sources/rank-5b-locators.md#propositions-33-and-34)
