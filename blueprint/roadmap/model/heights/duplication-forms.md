---
article_id: af_ce8bd6c6b4c823fa6d914a1a
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.F2, ZInQ.G2, ZInQ.x_two_smul_C
---

# The duplication forms on $C$

Put
$$F_2(a,b)=(a^2+\delta^2b^2)^2,\qquad G_2(a,b)=4ab(a^2-\delta^2b^2).$$
Let $T=(x,y)\in C(K_0)$ with $y\ne0$, and let $a,b\in\mathbb Z[s]$ with $b\ne0$ and $x=a/b$. Then
$G_2(a,b)\ne0$, $[2]T\ne O$ and
$$x([2]T)=\frac{F_2(a,b)}{G_2(a,b)} .$$
If instead $y=0$, then $[2]T=O$.

**Proof sketch.** With the tangent slope $\lambda=(3x^2-\delta^2)/(2y)$,
$x([2]T)=\lambda^2-2x=\frac{(3x^2-\delta^2)^2-8x(x^3-\delta^2x)}{4y^2}=\frac{(x^2+\delta^2)^2}{4x(x^2-\delta^2)}$,
using $y^2=x(x^2-\delta^2)$; homogenize with $x=a/b$. Since $y\ne0$, $x\notin\{0,\delta,-\delta\}$,
so $a\ne0$ and $a^2\ne\delta^2b^2$, hence $G_2(a,b)\ne0$. A point with $y=0$ equals its own
negative.

## Depends on

- [The change of variables to $C$](../descent/coordinate-change.md)

## Sources

- [Duplication bounds](../../../sources/model-locators.md#duplication-bounds)
