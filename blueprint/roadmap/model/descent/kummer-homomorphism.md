---
article_id: af_d914acd37b9b0a8050650a67
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Descent.kummer_add, ZInQ.Descent.kummerHom, ZInQ.Descent.mul_addX_eq, ZInQ.Descent.kummer_two_nsmul
---

# The Kummer map is a homomorphism

Let $K$ be a field of characteristic different from $2$ and $b\in K^\times$. The Kummer map
$\alpha_b:E_b(K)\to K^\times/K^{\times2}$ is a group homomorphism. In particular
$\alpha_b(2P)=1$ for every $P\in E_b(K)$.

Along the way: let $(x_1,y_1)$ and $(x_2,y_2)$ be affine points of $E_b(K)$ that are not negatives
of each other, let $\lambda$ be the slope of the chord (or tangent) through them, and let
$x_3=\lambda^2-x_1-x_2$ be the abscissa of their sum. Then $x_1x_2x_3=(y_1-\lambda x_1)^2$.

**Proof sketch.** (Silverman, Proposition X.4.9; Silverman-Tate, Section III.5.) Since
$\alpha_b(-P)=\alpha_b(P)$ and squareclasses have exponent two, it suffices to show
$\alpha_b(P_1)\alpha_b(P_2)\alpha_b(P_3)=1$ whenever $P_1+P_2+P_3=O$. If one of the points is
$O$ this is $\alpha_b(-P)=\alpha_b(P)$. Otherwise the three points are the intersections, with
multiplicity, of a line $y=\lambda x+\nu$ with $E_b$, so
$x^3+bx-(\lambda x+\nu)^2=(x-x_1)(x-x_2)(x-x_3)$ and $x_1x_2x_3=\nu^2$. If no $x_i$ is $0$ this
gives the claim ($\nu\ne0$). If some $P_i=(0,0)$, then $\nu=0$, the other two abscissas are
the roots of $x^2-\lambda^2x+b$, and their product is $b=\alpha_b((0,0))$ modulo squares. The
case analysis matches the chord, tangent and vertical cases of the addition law; in the
formula for $x(P+Q)$ via the slope, the identity follows from the factorization of the
cubic above, with $\nu=y_1-\lambda x_1$. Finally $\alpha_b(2P)=\alpha_b(P)^2=1$, since square classes
have exponent two.

## Depends on

- [Two-isogenies and the Kummer map](kummer-map.md)

## Sources

- [First descent image](../../../sources/model-locators.md#first-descent-image)
- [Silverman](../../../sources/model-locators.md#silverman)
