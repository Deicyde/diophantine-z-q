---
article_id: af_987059c28c264863daa0a483
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.rel_member_iff
---

# Polynomial membership in the doubled group

For every $p\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{member}}(p)\iff p=\operatorname{code}(Q)\ \text{for some }Q\in2E(K_0),$$
where $\mathrm{Rel}_{\mathtt{member}}(p)$ means that the polynomial of the membership template
vanishes at $p$ and some rational values of its seven witnesses $X=(X_0,X_1)$,
$Y=(Y_0,Y_1)$, $H=(H_0,H_1)$, $u$. This is an all-input statement: $p$ is an arbitrary
rational $5$-tuple, not assumed to be a code.

Explicitly, apart from the identity branch $p=(1,0,0,0,0)$, the template asks for
$X,Y,H\in K_0$ and $u\in\mathbb Q$ with
$$p_0=0,\quad Y^2=X^3-d^2X,\quad u\operatorname N(Y)=1,\quad 2YH=3X^2-d^2,\quad x=H^2-2X,\quad
y=H(X-x)-Y,$$
where $x=p_1+p_2s$, $y=p_3+p_4s$, each field equation being two rational equations (the
template writes the last as $y=H(X-(H^2-2X))-Y$, equivalent given the abscissa equation).

**Proof sketch.** The template polynomial is the square of the compilation of its formula,
so it vanishes exactly when one branch holds. If the identity branch holds,
$p=\operatorname{code}(O)$ and $O\in2E(K_0)$. If the doubling branch holds, $(X,Y)\in E(K_0)$,
$Y\ne0$ because $u\operatorname N(Y)=1$, $H=(3X^2-d^2)/(2Y)$ is the tangent slope, and $(x,y)$ is
given by the doubling formula, so $p=\operatorname{code}([2](X,Y))$. Conversely let $Q=[2]T$. If
$Q=O$, the identity branch holds with arbitrary witnesses. Otherwise $T=(X,Y)$ is affine
with $Y\ne0$, since a point with $Y=0$ has $[2]T=O$: every nonidentity double has a preimage
with nonzero ordinate. Take $H$ the tangent slope and $u=\operatorname N(Y)^{-1}$; the doubling
branch holds with $p=\operatorname{code}(Q)$.

## Depends on

- [The membership template](../syntax/template-member.md)
- [Point codes](point-codes.md)

## Proof depends on

- [Sums of squares and products over the rationals](../syntax/sum-of-squares-semantics.md)
- [Pair arithmetic represents the quadratic field](../syntax/field-pair-arithmetic.md)
- [Elementary properties of codes](field/point-code-properties.md)

## Sources

- [Membership and addition](../../sources/model-locators.md#membership-and-addition)
- [Translation typing](../../sources/model-locators.md#translation-typing)
