---
article_id: af_733e695433cc05b6359a1992
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.delta_eq_sqc_kummer, ZInQ.RouteK.Rank.kummer_fst_ne_zero, ZInQ.RouteK.Rank.kummer_snd_ne_zero
---

# The descent map is the Kummer map of the coverings

Let $K$ be a field with $2\ne0$ and $d\in K^\times$, and let
$k(P)=(k_1(P),k_2(P))\in K\times K$ be the Kummer map of the coverings of $C_d$: $(1,1)$ at $O$;
$(-1,-d)$, $(d,2)$, $(-d,-2d)$ at $(0,0)$, $(d,0)$, $(-d,0)$; and $(x,x-d)$ at every other point
$(x,y)$. Then for every $P\in C_d(K)$ both $k_1(P)$ and $k_2(P)$ are nonzero, and $\delta_d(P)$ is
the pair of their square classes.

**Proof sketch.** Compare the two maps point by point. At $O$ both give $(1,1)$. At $(0,0)$,
$\delta_d$ gives $(-d^2,-d)$, and $-d^2=(-1)\,d^2\equiv-1$. At $(d,0)$ it gives
$(d,3d^2-d^2)=(d,2d^2)\equiv(d,2)$. The point $(-d,0)$ has abscissa outside $\{0,d\}$ because
$d\ne0$ and $2d\ne0$, so $\delta_d$ gives $(-d,-d-d)=(-d,-2d)$. At every other point both maps give
$(x,x-d)$. The values $-1,-d,d,2,-2d$ are nonzero since $2\ne0$ and $d\ne0$, and $x$, $x-d$ are
nonzero off the torsion abscissas.

## Depends on

- [The complete 2-descent map of a congruent number curve](descent-map.md)
- [Coverings and the Kummer map](../../selmer/kummer-map.md)

## Proof depends on

- [The Kummer map at a root of the cubic](kummer-map-at-root.md)

## Sources

- [The complete 2-descent map](../../../sources/rank-locators.md#the-complete-2-descent-map)
- [The Kummer map](../../../sources/selmer-locators.md#the-kummer-map)
