---
article_id: af_d84360a4d58732e4ebd5b5e4
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.SqTest, ZInQ.isSquare_iff_sqTest
---

# An exact square test in $K_0$

For $u,v\in\mathbb Q$ say that $\mathrm{Sq}(u,v)$ holds if there are a sign $\eta\in\{1,-1\}$ and
rationals $t,y_0$ with
$$t^2=u^2-2v^2,\qquad y_0^2=\frac{u+\eta t}{2},$$
such that either $y_0\ne0$ and $\bigl(y_0+\tfrac{v}{2y_0}s\bigr)^2=u+vs$, or $y_0=0$, $v=0$ and
$u/2=y_1^2$ for some $y_1\in\mathbb Q$. Then
$$u+vs\ \text{is a square in }K_0\iff\mathrm{Sq}(u,v),$$
including the case $u+vs=0$. Since a rational number has a rational square root exactly when
its reduced numerator and denominator are perfect squares (and it is nonnegative),
$\mathrm{Sq}$ is decidable by finitely many integer square-root extractions.

**Proof sketch.** ($\Leftarrow$) In the first case the square is exhibited; in the second
$(y_1s)^2=2y_1^2=u=u+vs$. ($\Rightarrow$) If $u+vs=(y_0+y_1s)^2$, then $u=y_0^2+2y_1^2$,
$v=2y_0y_1$ and $u^2-2v^2=(y_0^2-2y_1^2)^2$. Take $t=|y_0^2-2y_1^2|$ and $\eta$ with
$\eta t=y_0^2-2y_1^2$; then $(u+\eta t)/2=y_0^2$. If $y_0\ne0$, $y_1=v/(2y_0)$; if $y_0=0$, then
$v=0$ and $u=2y_1^2$.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../field/quadratic-field.md)

## Sources

- [Finite search](../../../sources/model-locators.md#finite-search)
