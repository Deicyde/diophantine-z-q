---
article_id: af_d6739f06268bd37f40432af4
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Selmer.Cov, ZInQ.RouteK.Selmer.Loc, ZInQ.RouteK.Selmer.SqEq, ZInQ.RouteK.Selmer.SqEq.refl, ZInQ.RouteK.Selmer.SqEq.symm, ZInQ.RouteK.Selmer.SqEq.trans, ZInQ.RouteK.Selmer.SqEq.mul, ZInQ.RouteK.Selmer.sqEq_iff_isSquare_mul
---

# The 2-coverings of a congruent number curve

Let $K$ be a field and $d,a,b\in K$. The *2-covering* of $C_d:y^2=x^3-d^2x$ attached to $(a,b)$
is the curve in $\mathbb P^3$
$$D_{a,b}:\qquad az_1^2-bz_2^2=dw^2,\qquad az_1^2-abz_3^2=-dw^2 .$$
Say that $D_{a,b}$ is *soluble over $K$* when it has a $K$-point, that is a solution
$(z_1,z_2,z_3,w)\ne(0,0,0,0)$ in $K$.

Its *x-form* is the condition that either $a$ and $b$ are squares in $K$, or there is $x\in K$
such that $x/a$, $(x-d)/b$ and $(x+d)/(ab)$ are squares in $K$ (zero counts as a square).

For $u,v\in K$ write $u\equiv v$ when $u=vs^2$ for some nonzero $s\in K$. This is an equivalence
relation compatible with products, and for nonzero $u,v$ it says that $uv$ is a square.

## Depends on

None.

## Sources

- [Coverings](../../sources/selmer-locators.md#coverings)
