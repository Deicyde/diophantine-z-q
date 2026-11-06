---
article_id: af_29bde1829fd762ca6ea54475
declaration: lemma
origin: bridged
---

# The chord estimate in a formal neighbourhood

Let $K$ be a field with a discrete valuation $v$, let $A\in K$ with $v(A)\ge0$, and let
$k\ge1$. For affine points $P_1,P_2\in W_k(K)$ of $y^2=x^3+Ax$ with $P_1+P_2$ affine, write
$z=-x/y$ and $\omega=-1/y$. If $z(P_1)\ne z(P_2)$, the line through the points in the
$(z,\omega)$-plane is $\omega=\lambda z+\nu$ with $v(\lambda)\ge2k$ and $v(\nu)\ge3k$, and
$$z(P_1+P_2)=z(P_1)+z(P_2)+\frac{2A\lambda\nu}{1+A\lambda^2},\qquad
v\bigl(z(P_1+P_2)-z(P_1)-z(P_2)\bigr)\ge5k ;$$
for $P_1=P_2$ the same holds with the tangent line. In particular $W_k(K)$ is closed under
addition and $z$ is additive modulo valuation $5k$.

**Proof sketch.** This is the chord computation behind the canonical article on formal
neighbourhoods. In the coordinates $(z,\omega)$ the curve is $\omega=z^3+Az\omega^2$. The
slope of the chord satisfies $\lambda(z_2-z_1)=\omega_2-\omega_1$; expanding with the curve
equation and $v(z_i)\ge k$, $v(\omega_i)\ge3k$ gives $v(\lambda)\ge2k$, and then
$\nu=\omega_1-\lambda z_1$ has $v(\nu)\ge3k$. Substituting the line into the curve equation
gives a cubic in $z$ whose three roots are $z_1,z_2$ and $z_3$; by Vieta
$z_1+z_2+z_3=-2A\lambda\nu/(1+A\lambda^2)$, and $z(P_1+P_2)=-z_3$ because negation changes the
sign of $z$. The valuation bound follows from $v(1+A\lambda^2)=0$. The Lean lemma behind the
canonical article proves the bound $5k$ internally and exports only $k+1$; this article asks
for the sharp form.

## Depends on

- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](formal-group.md)

## Sources

- [Local conventions](../../../sources/multiplication-locators.md#local-conventions)
- [Silverman](../../../sources/multiplication-locators.md#silverman)
