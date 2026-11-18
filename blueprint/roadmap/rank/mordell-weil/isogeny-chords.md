---
article_id: af_d5c26ede4ff40c0a1afabc9e
declaration: lemma
origin: background
---

# The two-isogeny maps a chord to a chord

> **Retired with Route K.** This page described part of Route K, the project's earlier replacement for pole completeness through Tian–Yuan–Zhang and Gross–Zagier. The [main theorem](../../main/main-theorem.md) no longer uses it. Its Lean declarations were removed (fork issue #77) and are kept at the tag `route-k-final`.

Let $K$ be a field and $b,\ell,\nu\in K$ with $\nu\ne0$. Put
$$L=\frac b\nu-\ell,\qquad N=-\nu-\frac{b\ell^2}{\nu}.$$

1. (The image line.) If $x\ne0$, $y=\ell x+\nu$ and $y^2=x^3+bx$, then
   $X=y^2/x^2$ and $Y=y(b-x^2)/x^2$, the formulas of the two-isogeny $\varphi_b$ at $(x,y)$,
   satisfy $Y=LX+N$.
2. (The abscissa sum.) If $x_1,x_2,x_3\in K$ are nonzero and
   $$x_1+x_2+x_3=\ell^2,\qquad x_1x_2+x_1x_3+x_2x_3=b-2\ell\nu,\qquad x_1x_2x_3=\nu^2,$$
   then
   $$\sum_{i=1}^3\frac{(\ell x_i+\nu)^2}{x_i^2}=L^2 .$$
3. (Tangency.) If in 1 also $2y\ell=3x^2+b$, then $2LY=3X^2-4b$.

No assumption on the characteristic of $K$ or on $b$ is needed.

**Proof sketch.** Each identity becomes polynomial after clearing the nonzero denominators $x$
(or $x_1,x_2,x_3$) and $\nu$. In 1, substitute $y=\ell x+\nu$: the difference of the two sides is
a multiple of $y^2-x^3-bx$. In 2, use the first two relations to eliminate
$x_3=\ell^2-x_1-x_2$ and $b=x_1x_2+(x_1+x_2)x_3+2\ell\nu$; the difference is then a polynomial
multiple of $x_1x_2x_3-\nu^2$. In 3, use the tangency condition to eliminate
$b=2y\ell-3x^2$; the difference is a polynomial multiple of the curve equation.

## Depends on

- [Two-isogenies and the Kummer map](../../model/descent/kummer-map.md)

## Sources

- [Silverman-Tate](../../../sources/rank-locators.md#silverman-tate)
