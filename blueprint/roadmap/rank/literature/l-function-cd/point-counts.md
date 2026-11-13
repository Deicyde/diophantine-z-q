---
article_id: af_e0eeec1f0d939696540dd021
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Literature.equation_variableChange_iff, ZInQ.Literature.solutionsVariableChangeEquiv, ZInQ.Literature.pointEquivOption, ZInQ.Literature.natCard_point_variableChange, ZInQ.Literature.natCard_point_map_ringEquiv
---

# Point counts under changes of variables and field isomorphisms

Let $F$ be a field, $E$ a Weierstrass equation over $F$ and $C=(u,r,s,t)$ a change of variables
over $F$, with $C\cdot E$ as in
[minimal Weierstrass equations](minimal-models.md). The *points* of $E$ over $F$ are the point at
infinity and the nonsingular solutions $(x,y)\in F^2$ of $E$. The number of elements of an infinite
set is taken to be $0$.

1. For $x,y\in F$, $(x,y)$ is a solution of $C\cdot E$ if and only if
   $(u^2x+r,\ u^3y+su^2x+t)$ is a solution of $E$.
2. The map $(x,y)\mapsto(u^2x+r,\ u^3y+su^2x+t)$ is a bijection from the solutions of $C\cdot E$ in
   $F^2$ to those of $E$, with inverse
   $(x,y)\mapsto\bigl((x-r)/u^2,\ (y-s(x-r)-t)/u^3\bigr)$.
3. If $\Delta(E)\ne0$, the points of $E$ over $F$ are in bijection with the solutions of $E$ in
   $F^2$ together with one extra element (the point at infinity): every solution is nonsingular.
4. If $\Delta(E)\ne0$, then $C\cdot E$ and $E$ have the same number of points over $F$.
5. If $\Delta(E)\ne0$ and $f:F\to F'$ is an isomorphism of fields, then the equation $E^f$ over
   $F'$ obtained by applying $f$ to the coefficients has the same number of points over $F'$ as
   $E$ has over $F$.

**Proof sketch.** (1) Substitute the coefficients of $C\cdot E$ and clear the powers of $u\ne0$;
the two equations differ by the factor $u^6$. (2) The two maps are mutually inverse by direct
computation, and each preserves the equations by (1). (3) An equation with nonzero discriminant is
nonsingular at every solution. (4) By (3) for $E$ and for $C\cdot E$ (whose discriminant
$u^{-12}\Delta(E)$ is nonzero), and the bijection (2). (5) $f\times f$ maps the solutions of $E$
bijectively to those of $E^f$, and (3) adds the point at infinity on both sides.

## Depends on

- [Minimal Weierstrass equations over a discrete valuation ring](minimal-models.md)

## Sources

- [Minimal equations over a discrete valuation ring](../../../../sources/rank-locators.md#minimal-equations-over-a-discrete-valuation-ring)
