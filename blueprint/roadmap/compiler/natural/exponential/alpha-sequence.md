---
article_id: af_91330468ecd40d4439cb24f2
declaration: def
origin: background
statement: formalized
lean: ZInQ.AlphaPower.alphaZ, ZInQ.AlphaPower.alphaInt, ZInQ.AlphaPower.alphaInt_neg, ZInQ.AlphaPower.alphaInt_add_two
---

# The alpha sequence

For a natural number $b$ the *alpha sequence* $U_n=\alpha_b(n)\in\mathbb Z$, $n\in\mathbb N$, is
defined by
$$U_0=0,\qquad U_1=1,\qquad U_{n+2}=b\,U_{n+1}-U_n\quad(n\ge0).$$
It is integer-valued for every $b$ (its values may be negative when $b\in\{0,1\}$). The
matrix
$$M_b=\begin{pmatrix}b&-1\\1&0\end{pmatrix}$$
drives the recurrence: $M_b\,(U_n,U_{n-1})^{\mathsf T}=(U_{n+1},U_n)^{\mathsf T}$ for $n\ge1$.
When an index may be negative, the sequence is extended by $U_{-j}=-U_j$, which is
consistent with the recurrence.

This is a definition. It is the sequence of the Archive of Formal Proofs development used
by the manuscript; $U_{n+1}$ is the Chebyshev polynomial of the second kind $S_n$
(normalized by $S_{n+2}=XS_{n+1}-S_n$, $S_0=1$, $S_{-1}=0$) evaluated at $b$. Only natural
parameters $b$ occur in this chapter, and every natural-valued use (a witness of the alpha
formula) is justified by the growth lemma for $b\ge2$.

## Depends on

None.

## Sources

- [Section 10.2 alpha recurrence](../../../../sources/compiler-natural-locators.md#section-102-alpha-recurrence)
- [AFP DPRM development](../../../../sources/compiler-natural-locators.md#afp-dprm-development)
