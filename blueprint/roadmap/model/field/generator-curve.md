---
article_id: af_86ee84f1f3a5c8277b1c5ff7
declaration: def
origin: cited
statement: formalized
lean: ZInQ.genCurve, ZInQ.genCurve_two_torsion
---

# The generator curve $E$

Put $d=75-53s\in\mathbb Z[s]$, so that
$$d^2=11243-7950s,\qquad A:=-d^2=-11243+7950s,\qquad \operatorname N(d)=75^2-2\cdot53^2=7 .$$
The curve $E$ over $K_0$ is the short Weierstrass curve
$$E:\ y^2=x^3-d^2x=x^3+Ax .$$
Its discriminant $-64A^3=64d^6$ is nonzero, so $E$ is an elliptic curve. Its group of
$K_0$-rational points, with the usual chord-and-tangent law and identity $O$, is written
$E(K_0)$. Since $x^3-d^2x=x(x-d)(x+d)$, the points of order dividing two are
$$E(K_0)[2]=\{O,\ (0,0),\ (d,0),\ (-d,0)\}.$$

The group law is the standard one for $y^2=x^3+Ax$: $-(x,y)=(x,-y)$; if $x_1\ne x_2$ the
sum of $(x_1,y_1)$ and $(x_2,y_2)$ has $\lambda=(y_2-y_1)/(x_2-x_1)$; if the points are
equal with $y_1\ne0$, $\lambda=(3x_1^2+A)/(2y_1)$; in both cases
$x_3=\lambda^2-x_1-x_2$ and $y_3=\lambda(x_1-x_3)-y_1$; and $(x,y)+(x,-y)=O$.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](quadratic-field.md)

## Proof depends on

- [Explicit identities in $K_0$](explicit-identities.md)

## Sources

- [Model setup](../../../sources/model-locators.md#model-setup)
- [Point references and fixed point codes](../../../sources/model-locators.md#point-references-and-fixed-point-codes)
