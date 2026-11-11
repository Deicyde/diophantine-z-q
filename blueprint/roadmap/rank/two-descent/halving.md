---
article_id: af_16bc050ec4ead216b5e2fcab
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.exists_two_nsmul_eq_of_squares, ZInQ.RouteK.Rank.halve_identities, ZInQ.RouteK.Rank.some_eq_or_eq_neg
---

# The halving lemma

Let $K$ be a field with $2\ne0$ and $d\in K^\times$, and let $(x,y)\in C_d(K)$. If $x=r_1^2$,
$x-d=r_2^2$ and $x+d=r_3^2$ for some $r_1,r_2,r_3\in K$, then $(x,y)=2Q$ for some $Q\in C_d(K)$.

Along the way, over any field and for any $d$: two affine points of $C_d(K)$ with the same
abscissa are equal or opposite; and for $r_1,r_2,r_3\in K$ with $r_1^2+D=r_3^2$, where
$D=r_1^2-r_2^2$, and for $x'=r_1^2+r_1r_2+r_1r_3+r_2r_3$ and $y'=(r_1+r_2)(r_1+r_3)(r_2+r_3)$:
$y'^2=x'^3-D^2x'$ and $(3x'^2-D^2)^2=(r_1^2+2x')(2y')^2$.

**Proof sketch.** Take $x',y'$ as in the statement. Here $d=r_1^2-r_2^2$ and $r_1^2+d=r_3^2$, so the two polynomial identities hold with $D=d$. The first puts
$Q=(x',y')$ on $C_d$. Next, $y'\ne0$: $r_1+r_2=0$ would give $d=r_1^2-r_2^2=0$, $r_1+r_3=0$ would
give $d=r_3^2-r_1^2=0$, and $r_2+r_3=0$ would give $2d=r_3^2-r_2^2=0$. So $Q$ is not
$2$-torsion, $2Q$ is affine, and by the second identity its abscissa $\lambda^2-2x'$, with
$\lambda=(3x'^2-d^2)/(2y')$, equals $r_1^2=x$. Two points with the same abscissa have the same
$y^2$, so they are equal or opposite. Hence $(x,y)=2Q$ or $(x,y)=2(-Q)$.

## Depends on

- [Two-isogenies and the Kummer map](../../model/descent/kummer-map.md)

## Proof depends on

- [The complete 2-descent map of a congruent number curve](descent-map.md)

## Sources

- [Halving](../../../sources/rank-locators.md#halving)
