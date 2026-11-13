---
article_id: af_732b2d7656b98b06478e69fd
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.exists_infinite_order_iff_infinitelyManyPoints, ZInQ.RouteK.Rank.infinitelyManyPoints_iff_infinite_points, ZInQ.RouteK.Rank.infPtsMap_bijective, ZInQ.RouteK.Rank.infPtsMap, ZInQ.RouteK.Rank.infPts_nonsingular
---

# A point of infinite order exists iff there are infinitely many rational points

Let $d\ne0$ be a natural number and $C_d$ the curve $y^2=x^3-d^2x$ over $\mathbb Q$. Then $C_d(\mathbb Q)$
contains a point of infinite order if and only if $y^2=x^3-d^2x$ has infinitely many rational
solutions $(x,y)\in\mathbb Q^2$.

Along the way, for $d\ne0$:

- every rational solution $(x,y)$ of $y^2=x^3-d^2x$ is a nonsingular point of $C_d$;
- the map that sends one extra element to the point at infinity $O$ and each rational solution
  $(x,y)$ to the affine point $(x,y)$ is a bijection from the set of rational solutions with one
  extra element adjoined onto $C_d(\mathbb Q)$;
- hence $y^2=x^3-d^2x$ has infinitely many rational solutions if and only if $C_d(\mathbb Q)$ is
  infinite.

**Proof sketch.** The discriminant of $C_d$ is a nonzero multiple of $d^6$, hence nonzero, so every
solution of the equation is a nonsingular point. The points of $C_d(\mathbb Q)$ are $O$ and the
affine points, which are exactly the rational solutions; so the map above is a bijection, and the
solution set is infinite exactly when $C_d(\mathbb Q)$ is. If $P$ has infinite order, the multiples
$nP$ ($n\ge0$) are pairwise distinct, so $C_d(\mathbb Q)$ is infinite. Conversely, suppose every
point has finite order. By Mordell–Weil, $C_d(\mathbb Q)$ is finitely generated, and a finitely
generated abelian group in which every element has finite order is finite; so $C_d(\mathbb Q)$ is
finite, and there are only finitely many solutions.

## Depends on

- [Infinitely many rational solutions of $y^2=x^3-d^2x$](infinitely-many-points.md)

## Proof depends on

- [Mordell–Weil for the congruent number curves](../mordell-weil/finite-generation.md)

## Sources

- [The infinitely-many-points forms](../../../sources/rank-locators.md#the-infinitely-many-points-forms)
- [Mordell-Weil for the congruent number curves](../../../sources/rank-locators.md#mordell-weil-for-the-congruent-number-curves)
