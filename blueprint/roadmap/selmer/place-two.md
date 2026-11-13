---
article_id: af_d82d30c52ed71539c5914fec
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.loc_two_adic_iff, ZInQ.RouteK.Selmer.loc_two_adic_iff_of_odd, ZInQ.RouteK.Selmer.loc_two_adic_five
---

# Local solubility at the place 2

Let $d$ be an odd natural number (in particular $d\equiv5\pmod8$) and $a,b$ nonzero integers. Then
$D_{a,b}$ is soluble over $\mathbb Q_2$ (in its x-form) if and only if there are $i,j,k\in\{0,1\}$
such that $ad^i(-1)^j$ and $b\,2^i(-d)^j5^k$ are squares in $\mathbb Q_2$: the four torsion classes
and their products with $(1,5)$.

**Proof sketch.** (⇐) The torsion classes are soluble; the classes with $k=1$ have the rational
witnesses $x=1/4$, $d(1+4d)/(1-4d)$, $-4d^2$, $-d(1-4d)/(1+4d)$, for which the three quotients
are even powers of $2$ times rationals $\equiv1\pmod8$, hence squares by the rational test. (⇒)
After the torsion analysis, split on $v=v_2(x)$. For $v\le-3$ and $v\ge3$, (P) gives $(1,1)$ and
$(-1,-d)$. For $v=\pm1$ the norm of $x(x-d)(x+d)$ is an odd power of $2$. For $v=-2$, $x\mp d\equiv5x$,
giving $(1,5)$; for $v=2$, $x-d\equiv-5d$, $x+d\equiv5d$, giving $(-1,-5d)$. For $v=0$ one of
$x\mp d$ has norm $1/2$ and the other norm at most $1/8$, which gives $x\equiv\pm d$ and
$x\mp d\equiv\mp2d$ or $\mp10d$. Only "two 2-adic numbers of equal norm have a sum of smaller norm",
the discreteness of the norm and (P) are used.

## Depends on

- [The 2-coverings of a congruent number curve](coverings.md)

## Proof depends on

- [Squares in the p-adic numbers](padic-squares.md)
- [Square classes and torsion witnesses of a covering](covering-classes.md)

## Sources

- [The place 2](../../sources/selmer-locators.md#the-place-2)
