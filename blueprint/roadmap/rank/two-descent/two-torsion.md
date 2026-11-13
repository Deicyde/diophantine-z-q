---
article_id: af_62faee49c615a5b49d3742b8
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.card_ker_two_nsmul_eq_four, ZInQ.RouteK.Rank.ker_two_nsmul_eq, ZInQ.RouteK.Rank.delta_root_neg_d
---

# The two-torsion of a congruent number curve

Let $K$ be a field with $2\ne0$ and $d\in K^\times$. The points $P\in C_d(K)$ with $2P=O$ are
exactly $O$, $(0,0)$, $(d,0)$ and $(-d,0)$, and these are four distinct points; so $C_d(K)[2]$ has
exactly $4$ elements.

**Proof sketch.** The numbers $0$, $d$, $-d$ are roots of $x^3-d^2x$. An affine point satisfies
$2(x,y)=O$ exactly when $y=0$, which on $C_d$ means $x(x-d)(x+d)=0$, and a point whose abscissa is
a root is the corresponding torsion point $T_e$. The three affine points are distinct because
$d\ne0$ and $d\ne-d$ (as $2d\ne0$), and none of them is $O$.

## Depends on

- [Two-isogenies and the Kummer map](../../model/descent/kummer-map.md)

## Proof depends on

- [The Kummer map at a root of the cubic](kummer-map-at-root.md)
- [The complete 2-descent map of a congruent number curve](descent-map.md)

## Sources

- [Two-torsion of the congruent number curves](../../../sources/rank-locators.md#two-torsion-of-the-congruent-number-curves)
- [RK9](../../../sources/rank-locators.md#rk9)
