---
article_id: af_f426a59dca0cf2dcab5e536c
declaration: def
origin: background
statement: formalized
lean: ZInQ.RouteK.Rank.delta, ZInQ.RouteK.Rank.delta_root_zero, ZInQ.RouteK.Rank.delta_root_d, ZInQ.RouteK.Rank.delta_b_ne_zero
---

# The complete 2-descent map of a congruent number curve

Let $K$ be a field, $d\in K$, and $C_d:y^2=x^3-d^2x$, the curve $E_{-d^2}$. The numbers $0$ and
$d$ are roots of $x^3-d^2x$, and $-d^2\ne0$ when $d\ne0$. The *complete 2-descent map* of $C_d$ is
$$\delta_d:C_d(K)\to(K^\times/K^{\times2})^2,\qquad
\delta_d(P)=\bigl(\kappa_{-d^2,0}(P),\ \kappa_{-d^2,d}(P)\bigr).$$
Explicitly, for $d\ne0$: $\delta_d(O)=(1,1)$, $\delta_d((0,0))=(-d^2,-d)$,
$\delta_d((d,0))=(d,2d^2)$, and $\delta_d((x,y))=(x,x-d)$ for $x\notin\{0,d\}$, with the values
read modulo squares.

## Depends on

- [The Kummer map at a root of the cubic](kummer-map-at-root.md)

## Sources

- [The complete 2-descent map](../../../sources/rank-locators.md#the-complete-2-descent-map)
