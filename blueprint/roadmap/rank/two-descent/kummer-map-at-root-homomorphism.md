---
article_id: af_1791c5f472904e967cc025eb
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.kummerAt_add, ZInQ.RouteK.Rank.kummerAtHom, ZInQ.RouteK.Rank.kummerAt_neg, ZInQ.RouteK.Rank.kummerAt_root_ne_zero, ZInQ.RouteK.Rank.add_tRootPt_x, ZInQ.RouteK.Rank.kummerAt_add_tRootPt, ZInQ.RouteK.Rank.mul_addX_sub_eq
---

# The Kummer map at a root is a homomorphism

Let $K$ be a field with $2\ne0$, let $b\in K^\times$, and let $e\in K$ be a root of $x^3+bx$. Then
for all $P,Q\in E_b(K)$
$$\kappa_{b,e}(P+Q)=\kappa_{b,e}(P)\,\kappa_{b,e}(Q),$$
so $\kappa_{b,e}$ is a group homomorphism $E_b(K)\to K^\times/K^{\times2}$.

Along the way:

- $\kappa_{b,e}(-P)=\kappa_{b,e}(P)$ for every $P$ (for any field and any $b,e$);
- the root is simple: $3e^2+b\ne0$;
- for $(x,y)\in E_b(K)$ with $x\ne e$, the point $(x,y)+T_e$ has abscissa $e+(3e^2+b)/(x-e)$;
- $\kappa_{b,e}(P+T_e)=\kappa_{b,e}(P)\cdot(3e^2+b)$ for every $P$;
- (here $b=0$ is allowed) if $(x_1,y_1)$ and $(x_2,y_2)$ are points of $E_b(K)$ whose sum is affine,
  $\ell$ is the slope of the chord or tangent through them and $x_3$ is the abscissa of the sum,
  then $(x_1-e)(x_2-e)(x_3-e)=\bigl(y_1-\ell(x_1-e)\bigr)^2$.

**Proof sketch.** (Silverman, Proposition X.1.4.) $\kappa_{b,e}(-P)=\kappa_{b,e}(P)$ because negation
keeps the abscissa. Write $\kappa=\kappa_{b,e}$.

1. *Simple root.* If $3e^2+b=0$, then $e(e^2+b)=0$; $e=0$ gives $b=0$, and $e^2=-b$ gives $2b=0$,
   so $b=0$ either way.
2. *Translation by $T_e$.* For $x\ne e$ the chord through $(x,y)$ and $(e,0)$ gives the abscissa
   $e+(3e^2+b)/(x-e)$, which is not $e$ by step 1, so $\kappa(P+T_e)$ is the class of
   $(3e^2+b)/(x-e)$, that is of $(3e^2+b)(x-e)$. For $P=O$ the claim is $\kappa(T_e)=3e^2+b$. For
   $P=T_e$, $P+T_e=O$ and $(3e^2+b)^2$ is a square.
3. *Chord identity.* Expand the addition formulas, using the curve equations at the two points
   and $e^3+be=0$, in the chord case and in the tangent case.
4. *General case.* If $P$ or $Q$ is $O$ there is nothing to prove; if one of them is $T_e$, use
   step 2. If $Q=-P$, both sides are $1$. If $P+Q=T_e$, write $Q=-P+T_e$; step 2 and
   $\kappa(-P)=\kappa(P)$ give $\kappa(P)\kappa(Q)=\kappa(P)^2(3e^2+b)=\kappa(T_e)$. Otherwise the
   three abscissas differ from $e$, so $\nu=y_1-\ell(x_1-e)\ne0$ by step 3, and
   $x_3-e=(x_1-e)(x_2-e)\bigl(\nu/((x_1-e)(x_2-e))\bigr)^2$.

## Depends on

- [The Kummer map at a root of the cubic](kummer-map-at-root.md)

## Sources

- [The complete 2-descent map](../../../sources/rank-locators.md#the-complete-2-descent-map)
