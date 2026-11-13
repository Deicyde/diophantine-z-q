---
article_id: af_c6e302a5df326812e58418ad
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.det_border_eq_dotProduct, ZInQ.RouteK.Rank5b.border_mulVec_inl, ZInQ.RouteK.Rank5b.border_mulVec_inr, ZInQ.RouteK.Rank5b.zmod2_eq_zero_or_one'
---

# The bordered determinant (Lemma 4.2)

Let $M$ be a symmetric square matrix over $\mathbb F_2$ of corank one, whose kernel is
$\{0,k\}$ with $k\ne0$. Then for every vector $v$,
$$\det\begin{pmatrix}M&v\\ v^{\mathsf T}&0\end{pmatrix}=v\cdot k .$$

**Proof sketch.** If $v\cdot k=0$, the vector $(k,0)$ is a nonzero kernel vector of the bordered
matrix, whose determinant is therefore $0$. If $v\cdot k=1$, let $(w,t)$ be in the kernel:
$Mw+tv=0$ and $v\cdot w=0$. Pairing the first equation with $k$ and using
$k^{\mathsf T}M=(Mk)^{\mathsf T}=0$ gives $t(v\cdot k)=t=0$; then $Mw=0$, so $w\in\{0,k\}$, and
$v\cdot w=0\ne v\cdot k$ forces $w=0$. The kernel is trivial, so the determinant is the nonzero
element $1$ of $\mathbb F_2$. (The note's proof uses $\operatorname{adj}M=kk^{\mathsf T}$ instead.)

## Depends on

None.

## Sources

- [Lemma 4.2](../../sources/rank-5b-locators.md#lemma-42)
