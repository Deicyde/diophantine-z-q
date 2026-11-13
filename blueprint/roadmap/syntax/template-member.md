---
article_id: af_1db83f57595f0c0fba18bc86
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.memberTemplate, ZInQ.Syntax.memberTemplate_rel_iff
---

# The membership template

The template $\mathtt{member}$ has $5$ parameters and $7$ witnesses ($12$ variables). Its
variables are: the point $p=(X_0,\dots,X_4)$; the pairs $X=(X_5,X_6)$, $Y=(X_7,X_8)$ and
$H=(X_9,X_{10})$; and the inverse witness $u=X_{11}$ of $\mathrm{NZ}_K(Y)$. With
$x_P=H^2-2X$ and $y_P=H\cdot(X-x_P)-Y$, its formula is
$$\varphi_{\rm member}=\bigvee\Bigl(\mathrm{isO}(p),\ \bigwedge\bigl(\mathrm{fin}(p),\ \mathrm{curve}(X,Y),\
N(Y)\,u\doteq1,\ (2Y)\cdot H\doteq3X^2+A,\ x(p)\doteq x_P,\ y(p)\doteq y_P\bigr)\Bigr),$$
and, having no rational constants, its polynomial is $[\![\mathtt{member}]\!]=\kappa(\varphi_{\rm member})^2$.

The second branch says: $(X,Y)\in E(K_0)$ with $Y\ne0$, $H$ is the tangent slope at $(X,Y)$,
and $p$ is the code of the affine point $2(X,Y)$. That $\mathrm{Rel}_{\mathtt{member}}(p)$ holds
exactly for the codes of points of $2E(K_0)$ is the membership statement of the model
chapter.

This is a definition (template index $0$ of the library).

## Depends on

- [Formulas and their polynomial compilation](language/formula-compilation.md)
- [Quadratic-field pairs and point-code formulas](language/field-pair-gadgets.md)

## Sources

- [Section 3.1](../../sources/syntax-locators.md#section-31-membership-and-natural-codes)
- [Appendix C.2](../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Saved specification](../../sources/syntax-locators.md#saved-specification)
