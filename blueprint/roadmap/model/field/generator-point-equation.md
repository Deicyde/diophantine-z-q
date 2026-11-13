---
article_id: af_08fe96c4dcb911a6ada39272
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.genP0_equation
---

# The coordinates of $P_0$ satisfy the curve equation

Let $x_0=\frac{1641-1160s}{8}$ and $y_0=\frac{-123720+87483s}{32}$ in $K_0$. Then
$$y_0^2=x_0^3-d^2x_0\qquad(d^2=11243-7950s),$$
and $y_0\ne0$.

This is a closed identity between explicit elements of $K_0$: after expanding with
$s^2=2$, both components of $y_0^2-x_0^3+d^2x_0$ are explicit rationals, and the claim is
that both vanish. It is a finite computation.

**Proof sketch.** Expand both sides with the product rule of $K_0$ and compare the two
rational components. Alternatively, it follows from the certificate for $R$: the point
$2R$ of $C$ is sent by the inverse change of variables to $(x_0,y_0)$, and the change of
variables preserves the curve equations; that route needs no separate arithmetic, but the
direct expansion is shorter.

## Depends on

- [The generator curve $E$](generator-curve.md)

## Sources

- [Model setup](../../../sources/model-locators.md#model-setup)
