---
article_id: af_a196dae9d8011ff77fa16256
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.rawZ_rel_iff_of, ZInQ.Mult.rawZ_not_rel, ZInQ.Mult.rawInverseX_rel_iff_of, ZInQ.Mult.rawInverseX_not_rel, ZInQ.Mult.log25_rel_iff, ZInQ.Mult.rawZ_rel_iota, ZInQ.Mult.rawInverseX_rel_iota
---

# Semantics of the local-parameter, inverse-abscissa and logarithm templates

Let $Q\in E(K_0)$ with code $p=\operatorname{code}(Q)$, and let $\zeta,v,\lambda$ be rational
pairs, $[u]=u_0+u_1s$.

1. If $Q=O$ or $y(Q)\ne0$, then $\mathrm{Rel}_{\mathtt{raw\_z}}(p,\zeta)\iff[\zeta]=z(Q)$, where
   $z(O)=0$ and $z(Q)=-x(Q)/y(Q)$. If $Q$ is affine with $y(Q)=0$, the relation fails for
   every $\zeta$.
2. If $Q=O$ or $x(Q)\ne0$, then $\mathrm{Rel}_{\mathtt{raw\_inverse\_x}}(p,v)\iff[v]=1/x(Q)$,
   with value $0$ at $O$. If $Q$ is affine with $x(Q)=0$, the relation fails for every $v$.
3. For all pairs $\zeta,\lambda$: $\mathrm{Rel}_{\mathtt{log25}}(\zeta,\lambda)\iff[\lambda]=L([\zeta])$.

In particular, for $Q\in\mathbb ZP_0$ (assuming the generator certificate, so that a
nonidentity multiple of $P_0$ has $x,y\ne0$) the three templates compute $z(Q)$, $1/x(Q)$
and $L(z(Q))$.

**Proof sketch.** Each template polynomial is the square of the compilation of its formula
($Z(p,\zeta)$ with one fresh variable, $I\!X(p,v)$, and the pair equation $L(\zeta)\doteq\lambda$),
so it vanishes exactly when the formula holds. The pair-arithmetic theorem describes
$Z(p,\zeta)$ and $I\!X(p,v)$ exactly: the identity branch applies iff $p=O$, and the affine
branch requires $[y(p)]\ne0$, resp. $[x(p)][v]=1$. For (3), pair arithmetic represents the
field operations, so the two components of $L(\zeta)-\lambda$ vanish iff $[\lambda]=L([\zeta])$.

## Depends on

- [The local parameter template](../../syntax/templates/template-raw-z.md)
- [The inverse abscissa template](../../syntax/templates/template-raw-inverse-x.md)
- [The truncated logarithm template](../../syntax/templates/template-log25.md)
- [Point codes](../../model/point-codes.md)
- [Semantics of templates and recipes](../../syntax/template-semantics.md)

## Proof depends on

- [Pair arithmetic represents the quadratic field](../../syntax/field-pair-arithmetic.md)
- [Sums of squares and products over the rationals](../../syntax/sum-of-squares-semantics.md)
- [Elementary properties of codes](../../model/field/point-code-properties.md)

## Sources

- [Twelve tests](../../../sources/multiplication-locators.md#twelve-tests)
- [Multiplication certificate generator](../../../sources/multiplication-locators.md#multiplication-certificate-generator)
