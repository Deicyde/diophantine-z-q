---
article_id: af_39ef01931d4fb7c8636a4d4a
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Descent.rescale_phi_phi, ZInQ.phiHatE_phiE, ZInQ.Descent.kummer_rescale
---

# The composite of the two-isogenies is doubling

Let $K$ be a field of characteristic different from $2$ and $b\in K^\times$. For every
$P\in E_b(K)$,
$$\lambda_b\Bigl(\varphi_{-4b}\bigl(\varphi_b(P)\bigr)\Bigr)=[2]P .$$
In particular, for $b=-d^2$ over $K_0$, $\hat\varphi\circ\varphi=[2]$ on $E(K_0)$. The rescaling
preserves the Kummer map: $\alpha_b(\lambda_b(P))=\alpha_{16b}(P)$ for every $P\in E_{16b}(K)$.

**Proof sketch.** If $P=O$ or $P=(0,0)$ both sides are $O$. If $P=(x,0)$ with $x\ne0$, then
$\varphi_b(P)=(0,0)$, its image under $\varphi_{-4b}$ is $O$, and $[2]P=O$. If $P=(x,y)$
with $x,y\ne0$, then $\varphi_b(P)=(X,Y)$ with $X=y^2/x^2\ne0$, and
$\lambda_b(\varphi_{-4b}(X,Y))=\bigl(Y^2/(4X^2),\,Y(-4b-X^2)/(8X^2)\bigr)$. Substituting and using
$y^2=x^3+bx$ gives $Y^2/(4X^2)=(x^2-b)^2/(4y^2)$, the abscissa of $[2]P$ for the tangent slope
$(3x^2+b)/(2y)$, and the ordinate agrees likewise; both are polynomial identities after
clearing the nonzero denominators $x$ and $y$. For the Kummer maps, $\lambda_b$ sends a point
with abscissa $x\ne0$ to one with abscissa $x/4$, in the same square class, and sends $(0,0)$ to
$(0,0)$, where the two maps take the values $b$ and $16b$, again in the same class.

## Depends on

- [Two-isogenies and the Kummer map](kummer-map.md)

## Sources

- [Descent index](../../../sources/model-locators.md#descent-index)
- [Silverman](../../../sources/model-locators.md#silverman)
