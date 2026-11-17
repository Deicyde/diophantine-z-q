---
article_id: af_347612b60d11e0f53cbbd819
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves31.pazukiCor13Upper
---

# Pazuki's comparison of the theta height with the Faltings height

The *Pazuki statement* is the following assertion. Let $A$ be an abelian surface over a number field
$K$, $\sigma:K\to\mathbb C$ an embedding, $\Lambda$ the kernel of a uniformization of $A_\sigma$ and
$\Omega\in\mathfrak H_2$ a period matrix of $\Lambda$. Let $z=(z_m)$, indexed by the characteristics
of level $2$, have coordinates in a number field $F\subset\mathbb C$, with
$z_m=c\,\theta_m(0,\Omega)$ for all $m$ and some $c\ne0$, and let $h_2(z)$ be its absolute
logarithmic height, with the $L^2$ norm at the archimedean places. Put $a=\max(1,h_2(z))$ and
$b=\max(1,h_F(A)+\log\pi)$. Then
$$a-\tfrac b2\le C_2\log\bigl(\min(a,b)+2\bigr),\qquad C_2=1000\cdot2^4(\log2^4)^5.$$

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. It is the upper half of the printed corollary. Reaching
it from the print takes reading an analytic principal polarization of $\mathbb C^2/\Lambda$ as an
algebraic one (Appell–Humbert and Lefschetz with GAGA, and the equality of the Néron–Severi groups
of $A$ over $\overline{\mathbb Q}$ and over $\mathbb C$), and showing that the uniformization is
biholomorphic. If the level-$2$ theta coordinates in Pazuki's paper are the second-order ones, this
statement is about $\log4$ stronger than the print, and whether the argument tolerates the weaker
constant has not been checked. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Pazuki bound](../../../sources/height-decomposition-locators.md#pazuki-bound)
