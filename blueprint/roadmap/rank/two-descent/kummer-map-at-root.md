---
article_id: af_16db888f0232d0ebd6c3844d
declaration: def
origin: background
statement: formalized
lean: ZInQ.RouteK.Rank.kummerAt, ZInQ.RouteK.Rank.kummerAt_zero, ZInQ.RouteK.Rank.kummerAt_some, ZInQ.RouteK.Rank.kummerAt_some_of_ne, ZInQ.RouteK.Rank.kummerAt_some_eq, ZInQ.RouteK.Rank.tRootPt, ZInQ.RouteK.Rank.tRootPt_def, ZInQ.RouteK.Rank.kummerAt_tRoot_equation, ZInQ.RouteK.Rank.kummerAt_y_eq_zero, ZInQ.RouteK.Rank.some_eq_tRootPt, ZInQ.RouteK.Rank.kummerAt_tRootPt
---

# The Kummer map at a root of the cubic

Let $K$ be a field, $b,e\in K$, and $E_b:y^2=x^3+bx$. Write $K^\times/K^{\times2}$
multiplicatively, and let the class of $0$ be $1$. The *Kummer map at $e$* is the map
$\kappa_{b,e}:E_b(K)\to K^\times/K^{\times2}$ given by
$$\kappa_{b,e}(O)=1,\qquad
\kappa_{b,e}\bigl((x,y)\bigr)=\begin{cases}3e^2+b, & x=e,\\ x-e, & x\ne e,\end{cases}$$
with the values read modulo squares.

Suppose that $e$ is a root of the cubic, $e^3+be=0$. Then $(e,0)$ satisfies the equation of $E_b$,
and every point $(x,y)\in E_b(K)$ with $x=e$ has $y=0$. If moreover $2\ne0$ and $b\ne0$, then
$(e,0)$ is a point $T_e\in E_b(K)$, every point $(x,y)\in E_b(K)$ with $x=e$ equals $T_e$, and
$\kappa_{b,e}(T_e)$ is the class of $3e^2+b$.

**Proof sketch.** The equation at $(e,0)$ reads $0=e^3+be$. A point $(e,y)$ on $E_b$ has
$y^2=e^3+be=0$, so $y=0$, and the point is $T_e$. The value at $T_e$ is the first case of the
definition.

## Depends on

- [Two-isogenies and the Kummer map](../../model/descent/kummer-map.md)

## Sources

- [The complete 2-descent map](../../../sources/rank-locators.md#the-complete-2-descent-map)
