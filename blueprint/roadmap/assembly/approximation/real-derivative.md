---
article_id: af_535faba1774d5ef403d98fe6
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Assembly.zCoord, ZInQ.Assembly.z_ratio_tendsto
---

# The derivative of multiplication at a real place

Let $\tau\in\{\sigma_+,\sigma_-\}$ be a real embedding of $K_0$ and $n$ a nonzero integer. For every
$\eta>0$ there is $M\in\mathbb R$ such that for every affine point $Q=(x,y)\in E(K_0)$ with
$\tau(x)>M$:

1. $x\ne0$, $y\ne0$, and $[n]Q$ is affine with nonzero abscissa and ordinate;
2. $\bigl|\tau\bigl(z([n]Q)/z(Q)\bigr)-n\bigr|<\eta$.

This is the statement that the derivative of $[n]$ at the identity is $n$, read in the
coordinate $z=-x/y$ near $O$ at the real place $\tau$.

**Proof sketch.** Write $f_m$ for the normalized division polynomials of $y^2=x^3+Ax$,
$A=-d^2$, and $\psi_m$ for the division polynomials. Since $z(-P)=-z(P)$, it suffices to treat
$n\ge1$. By the multiplication-by-$n$ formulas, if $\psi_n(Q)\ne0$ then $[n]Q$ is affine with
$$\frac{x([n]Q)}{x}=\frac{\phi_n(x)}{x\,\psi_n^2(x)},\qquad
\frac{y([n]Q)}{y}=\frac{f_{2n}(x)}{\psi_n^4(x)},$$
where $\phi_n=x\psi_n^2-\psi_{n+1}\psi_{n-1}$, and $\psi_n^2$, $\psi_n^4$ and $\phi_n$ are polynomials in $x$
after substituting $y^2=x^3+Ax$ (the second identity is $y([n]Q)=\psi_{2n}/(2\psi_n^4)$ with
$\psi_{2n}=2yf_{2n}$). By the agreement with the classical division polynomials, the degrees
and leading coefficients are: $\phi_n$ degree $n^2$, leading coefficient $1$; $\psi_n^2$ degree
$n^2-1$, leading coefficient $n^2$; $f_{2n}$ degree $2n^2-2$, leading coefficient $n$; $\psi_n^4$
degree $2n^2-2$, leading coefficient $n^4$ (for odd $n$ it is $f_n^4$, for even $n$ it is
$16(x^3+Ax)^2f_n^4$, and $f_n$ has leading coefficient $n$ or $n/2$). Apply $\tau$ to the
coefficients: as $\tau(x)\to+\infty$ the two quotients tend to $1/n^2$ and $1/n^3$, and
$\tau(\psi_n(x)^2)\ne0$, $\tau(y^2)=\tau(x)(\tau(x)^2-\tau(d)^2)>0$ for $\tau(x)$ large. Hence for
$\tau(x)>M$ all quantities are nonzero, and
$$\tau\Bigl(\frac{z([n]Q)}{z(Q)}\Bigr)=\tau\Bigl(\frac{x([n]Q)}{x}\Bigr)\Big/\tau\Bigl(\frac{y([n]Q)}{y}\Bigr)\longrightarrow\frac{n^3}{n^2}=n .$$
The polynomials depend only on $n$ and $A$, so $M$ depends only on $n$, $\tau$ and $\eta$.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)
- [The local parameter z on multiples of the generator](../../compiler/natural/precision/z-coordinate.md)
- [The generator curve $E$](../../model/field/generator-curve.md)

## Proof depends on

- [Division polynomials compute multiples](../../model/field/division-polynomial-multiples.md)
- [Normalized division polynomials and their components](../../syntax/division-polynomials.md)
- [Agreement with the classical division polynomials](../../syntax/division-polynomials-classical.md)

## Sources

- [Section 11.1 approximation](../../../sources/assembly-locators.md#section-111-approximation)
- [Silverman](../../../sources/assembly-locators.md#silverman)
