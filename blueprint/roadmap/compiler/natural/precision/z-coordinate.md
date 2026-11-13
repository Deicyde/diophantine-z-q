---
article_id: af_eff2db8faa62e4f285499545
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.Precision.zPt, ZInQ.Compiler.Precision.zPt_ne_zero, ZInQ.Compiler.Precision.Admissible, ZInQ.Compiler.Precision.zIdx, ZInQ.Compiler.Precision.epsIdx, ZInQ.Compiler.Precision.rRatio, ZInQ.Compiler.Precision.rRatio_eq_half_trace
---

# The local parameter z on multiples of the generator

Let $E:y^2=x^3+Ax$ over $K_0$ with $A=-d^2$, and $P_0$ the fixed point.

1. For an affine point $P=(x,y)\in E(K_0)$ with $y\ne0$ put $z(P)=-x/y\in K_0$. Such a point
   has $x\ne0$ (if $x=0$ then $y^2=0$), so $z(P)\ne0$; and $z(-P)=-z(P)$.
2. An index $k\in\mathbb Z$ is *admissible* if $[k]P_0$ is an affine point with nonzero
   ordinate. For admissible $k$ write
   $$z_k=z([k]P_0)=u_k+v_ks\quad(u_k,v_k\in\mathbb Q),\qquad \epsilon_k=|u_k|+|v_k|>0 .$$
3. For admissible $a$ and $j$ put
   $$r(a,j)=\tfrac12\operatorname{Tr}_{K_0/\mathbb Q}\frac{z_j}{z_a}\in\mathbb Q,$$
   the rational component of $z_j/z_a$.

This is a definition. The manuscript defines $z$ on nonzero multiples of $P_0$, where it is
well defined because $P_0$ has infinite order (no nonzero multiple is the identity or a
point of order two); admissibility makes this explicit, so that the precision relation
and its computation do not depend on the generator theorem.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../../model/field/quadratic-field.md)
- [The generator curve $E$](../../../model/field/generator-curve.md)
- [The point $P_0$](../../../model/field/generator-point.md)

## Sources

- [Section 10 decision predicate](../../../../sources/compiler-natural-locators.md#section-10-decision-predicate)
