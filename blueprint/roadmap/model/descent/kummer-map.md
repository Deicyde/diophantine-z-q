---
article_id: af_14c30b3d5c79807870ed9bb5
declaration: def
origin: background
statement: formalized
lean: ZInQ.Descent.SqClass, ZInQ.Descent.sqc, ZInQ.Descent.kummer, ZInQ.Descent.phi, ZInQ.Descent.rescale
---

# Two-isogenies and the Kummer map

Let $K$ be a field of characteristic different from $2$ and $b\in K^\times$, and let
$E_b:y^2=x^3+bx$ (an elliptic curve: its discriminant is $-64b^3\ne0$). Write
$K^\times/K^{\times2}$ multiplicatively.

- The *Kummer map* (the $x$-squareclass map) $\alpha_b:E_b(K)\to K^\times/K^{\times2}$ is
  $$\alpha_b(O)=1,\qquad \alpha_b\bigl((0,0)\bigr)=b\,K^{\times2},\qquad
  \alpha_b\bigl((x,y)\bigr)=x\,K^{\times2}\ \ (x\ne0).$$
- The *two-isogeny* $\varphi_b:E_b\to E_{-4b}$ is
  $$\varphi_b(O)=\varphi_b\bigl((0,0)\bigr)=O,\qquad
  \varphi_b\bigl((x,y)\bigr)=\Bigl(\frac{y^2}{x^2},\ \frac{y(b-x^2)}{x^2}\Bigr)\ \ (x\ne0).$$
  Its values lie on $E_{-4b}:Y^2=X^3-4bX$, by the identity
  $y^2(b-x^2)^2x^2=y^6-4bx^4y^2$ for $y^2=x^3+bx$.
- The *rescaling* $\lambda_b:E_{16b}\to E_b$ is $\lambda_b(O)=O$,
  $\lambda_b((x,y))=(x/4,\,y/8)$; it is a group isomorphism (the change of coordinates
  $(x,y)\mapsto(u^2x,u^3y)$ with $u=1/2$), with inverse $(x,y)\mapsto(4x,8y)$.

In this chapter $b=-d^2$ gives $E=E_{-d^2}$, $E'=E_{4d^2}:y^2=x^3+4d^2x$, the isogeny
$\varphi=\varphi_{-d^2}:E\to E'$ and the dual isogeny
$\hat\varphi=\lambda_{-d^2}\circ\varphi_{4d^2}:E'\to E_{-16d^2}\to E$; and $b=-\delta^2$ gives
the curve $C=E_{-\delta^2}$.

## Depends on

None.

## Sources

- [First descent image](../../../sources/model-locators.md#first-descent-image)
- [Descent index](../../../sources/model-locators.md#descent-index)
- [Silverman](../../../sources/model-locators.md#silverman)
