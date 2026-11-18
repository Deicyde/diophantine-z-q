---
article_id: af_0a08a40bf92dd1abcec8a308
declaration: lemma
origin: background
---

# Addition along a line on $E_c$

> **Retired with Route K.** This page described part of Route K, the project's earlier replacement for pole completeness through Tian–Yuan–Zhang and Gross–Zagier. The [main theorem](../../main/main-theorem.md) no longer uses it. Its Lean declarations were removed (fork issue #77) and are kept at the tag `route-k-final`.

Let $K$ be a field and $c,L,N\in K$, and let $E_c:Y^2=X^3+cX$, with the chord-and-tangent
addition on its nonsingular points. Let $(X_1,Y_1)$ and $(X_3,Y_3)$ be nonsingular points of
$E_c$ with
$$Y_1=LX_1+N,\qquad Y_3=-(LX_3+N).$$

1. If $(X_2,Y_2)$ is a nonsingular point of $E_c$ with $Y_2=LX_2+N$, $X_1\ne X_2$ and
   $X_1+X_2+X_3=L^2$, then $(X_1,Y_1)+(X_2,Y_2)=(X_3,Y_3)$.
2. If $2\ne0$ in $K$, $Y_1\ne0$, $2LY_1=3X_1^2+c$ and $2X_1+X_3=L^2$, then
   $2(X_1,Y_1)=(X_3,Y_3)$.

**Proof sketch.** This is the chord-and-tangent law on $E_c$, whose only nonzero Weierstrass
coefficient is $a_4=c$. In 1 the chord has slope $(Y_1-Y_2)/(X_1-X_2)=L$, so the sum has abscissa
$L^2-X_1-X_2=X_3$ and ordinate $-(Y_1+L(X_3-X_1))=-(LX_3+N)=Y_3$. In 2, $2Y_1\ne0$ gives
$Y_1\ne-Y_1$, so the doubling formula applies with tangent slope $(3X_1^2+c)/(2Y_1)=L$, and the
same computation gives $(X_3,Y_3)$.

## Depends on

None.

## Sources

- [Silverman-Tate](../../../sources/rank-locators.md#silverman-tate)
