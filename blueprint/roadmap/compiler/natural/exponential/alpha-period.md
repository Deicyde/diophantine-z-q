---
article_id: af_cad19badf98631e4fe9ed6b6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.AlphaPower.alphaZ_period, ZInQ.AlphaPower.alphaZ_reflection, ZInQ.AlphaPower.alphaZ_folded_residue, ZInQ.AlphaPower.two_mul_alphaZ_lt_companion'
---

# Period and reflection modulo the companion

Let $b>2$ be a natural number, $U_n=\alpha_b(n)$, $m>0$, and put
$$v=U_{m+1}-U_{m-1}=\operatorname{tr}(M_b^m)=bU_m-2U_{m-1}.$$

1. (Folding) Every $n\in\mathbb N$ can be written as $n=2lm+j$, or as $n=2lm-j$ with
   $0<j<2lm$, for some $l\in\mathbb N$ and $0\le j\le m$.
2. (Period and reflection) For all $l,j\in\mathbb N$,
   $$U_{j+2lm}\equiv(-1)^lU_j\pmod v,\qquad U_{2lm-j}\equiv-(-1)^lU_j\pmod v\ \ (0<j<2lm).$$
   Consequently, for $n$ folded as in item 1, $U_n\equiv\pm U_j\pmod v$.
3. (Bounds) If $b>3$ then $2U_j<v$ for every $0\le j\le m$; in particular $v>2U_m$.

The value sign in item 2 need not equal the index sign. In the manuscript's notation,
$n=2lm+\varepsilon j$ with $\varepsilon\in\{1,-1\}$ and $U_n\equiv(-1)^l\varepsilon U_j$.

**Proof sketch.** (1) Take $l$ with $2lm\le n<2(l+1)m$ and fold to the nearer of $2lm$ and
$2(l+1)m$. (2) $M^m$ has determinant $1$ and trace $v$, so by Cayley-Hamilton
$M^{2m}=vM^m-I\equiv-I\pmod v$, hence $M^{2lm}\equiv(-1)^lI$. The lower-left entry of
$M^{j+2lm}=M^jM^{2lm}$ gives the period congruence. For the reflection, the lower-left
entry of $M^{2lm}M^{-j}$, where $M^{-j}$ is the inverse matrix (entries in $\mathbb Z$ since
$\det M=1$), equals $U_{2lm-j}$ and is congruent to $(-1)^l\cdot(-U_j)$. In terms of the
recurrence alone: the identity $U_{n+2m}+U_n=vU_{n+m}$ (the addition formula) gives the
period, and $U_{N-j}=U_N(-U_{j-1})+(-U_{N-1})(-U_j)$ with $N=2lm$, $U_N\equiv0$,
$U_{N-1}\equiv-(-1)^l$, gives the reflection. (3) For $j\le m$, $2U_j\le2U_m$, and
$v-2U_m=(b-2)U_m-2U_{m-1}\ge2(U_m-U_{m-1})>0$ when $b\ge4$, using strict growth.

## Depends on

- [The alpha sequence](alpha-sequence.md)

## Proof depends on

- [Matrix powers and the quadratic identity](alpha-matrix.md)
- [Growth of the alpha sequence](alpha-growth.md)

## Sources

- [Section 10.2 period and reflection](../../../../sources/compiler-natural-locators.md#section-102-period-and-reflection)
