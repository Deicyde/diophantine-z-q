---
article_id: af_c0a94b1459f7c9e2ebfd9c2f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.curveC, ZInQ.theta, ZInQ.theta_some, ZInQ.curveC_two_torsion, ZInQ.two_nsmul_theta_eq_zero_iff, ZInQ.kummer_theta
---

# The change of variables to $C$

Let $\epsilon=1+s$, $\delta=3-s$ and $C=E_{-\delta^2}:y^2=x^3-\delta^2x$ over $K_0$. Then
$\epsilon^4=17+12s$, $\epsilon^6=99+70s$, $\delta=\epsilon^4d$, and the map
$$\theta:E(K_0)\to C(K_0),\qquad \theta(O)=O,\quad \theta(x,y)=(\epsilon^4x,\ \epsilon^6y)$$
is an isomorphism of groups, with inverse $(x,y)\mapsto(\epsilon^{-4}x,\epsilon^{-6}y)$. It maps
$E(K_0)[2]$ onto $C(K_0)[2]=\{O,(0,0),(\delta,0),(-\delta,0)\}$ and satisfies
$\alpha_{-\delta^2}(\theta(P))=\alpha_{-d^2}(P)$ for every $P\in E(K_0)$.

**Proof sketch.** $(75-53s)(17+12s)=3-s$ and $\epsilon^6=\epsilon^2\epsilon^4=(3+2s)(17+12s)$. For
$y^2=x^3-d^2x$, multiplying by $\epsilon^{12}$ gives
$(\epsilon^6y)^2=(\epsilon^4x)^3-\epsilon^8d^2(\epsilon^4x)$ and $\epsilon^8d^2=\delta^2$; the converse is
the same computation, $\epsilon$ being a unit. The map preserves the group law because chord
and tangent slopes are multiplied by $\epsilon^2$ (for the tangent slope use
$3(\epsilon^4x)^2-\delta^2=\epsilon^8(3x^2-d^2)$), so the sum formulas
$x_3=\lambda^2-x_1-x_2$, $y_3=\lambda(x_1-x_3)-y_1$ scale by $\epsilon^4$ and $\epsilon^6$; vertical
pairs go to vertical pairs. Two-torsion points have $y=0$ and abscissas $0,\pm d$, sent to
$0,\pm\delta$. Abscissas are multiplied by the square $\epsilon^4$, and $(0,0)$ has class $-d^2$
on $E$ and $-\delta^2$ on $C$, both equal to $-1$ modulo squares.

## Depends on

- [The generator curve $E$](../field/generator-curve.md)
- [Two-isogenies and the Kummer map](kummer-map.md)

## Proof depends on

- [Explicit identities in $K_0$](../field/explicit-identities.md)

## Sources

- [First descent image](../../../sources/model-locators.md#first-descent-image)
- [Transfer to the generator](../../../sources/model-locators.md#transfer-to-the-generator)
