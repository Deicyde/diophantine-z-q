---
article_id: af_a66e1c49f09946a83fb208f2
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Density.four_dvd_pointCount, ZInQ.Density.four_dvd_pointCount_of_mod_four
---

# Four divides the point count of $y^2=x^3-D^2x$

Let $p$ be an odd prime and $D\in\mathbb F_p^\times$. Then $4$ divides the number of points, the point
at infinity included, of $y^2=x^3-D^2x$ over $\mathbb F_p$.

The research note states this for $p\equiv1\pmod4$; the proof needs only that $p$ is odd.

**Proof sketch.** Put $g(x)=x(x-D)(x+D)$, with three distinct roots. Counting row by row, the
point count is $1+3+2m$ with $m=\#X$, $X=\{x\in\mathbb F_p^\times: g(x)\text{ a nonzero square}\}$.
The involution $\tau(x)=-D^2/x$ of $\mathbb F_p^\times$ satisfies $g(\tau x)=(D^2/x^2)^2g(x)$, so
$\tau(X)=X$, and an involution has $\#X\equiv\#\mathrm{Fix}(\tau|_X)\pmod 2$. The fixed points are the
solutions of $x^2=-D^2$: none for $p\equiv3\pmod4$, and $\pm iD$ for $p\equiv1\pmod4$, which lie in
$X$ together or not at all because $g$ is odd and $\chi(-1)=1$. So $m$ is even and $4\mid4+2m$.

## Depends on

None.

## Proof depends on

- [Character sums for the curves $y^2=x^3+ax$](character-sums.md)

## Sources

- [Character sums](../../sources/density-locators.md#character-sums)
