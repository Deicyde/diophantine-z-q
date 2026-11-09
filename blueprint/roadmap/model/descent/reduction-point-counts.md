---
article_id: af_c136be2068cbf05c7b361b76
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.pointCounts_17_23
---

# Point counts at $(17,s-6)$ and $(23,s-5)$

The following closed statements hold:

1. $6^2\equiv2\pmod{17}$ and $5^2\equiv2\pmod{23}$;
2. modulo $17$ with $s\mapsto6$: $d\mapsto75-53\cdot6\equiv12$ and $-d^2\mapsto-144\equiv-8\ne0$;
   modulo $23$ with $s\mapsto5$: $d\mapsto75-53\cdot5\equiv17$ and $-d^2\mapsto-289\equiv-13\ne0$;
3. the curve $y^2=x^3-8x$ over $\mathbb F_{17}$ has exactly $20$ points, and the curve
   $y^2=x^3-13x$ over $\mathbb F_{23}$ has exactly $24$ points, counting the point at
   infinity; that is,
   $$\#\{(x,y)\in\mathbb F_{17}^2:y^2=x^3-8x\}=19,\qquad
   \#\{(x,y)\in\mathbb F_{23}^2:y^2=x^3-13x\}=23 .$$

So $E$ has good reduction at the primes $(17,s-6)$ and $(23,s-5)$, with $20$ and $24$ points.
This is a finite computation.

**Proof sketch.** Direct evaluation; for (3), enumerate the $17^2$ and $23^2$ pairs.

## Depends on

None.

## Sources

- [Torsion bound](../../../sources/model-locators.md#torsion-bound)
