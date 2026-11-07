---
article_id: af_62e71107b1d0803f487f9922
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.tower_bounds, ZInQ.Size.degree_lt_tower_seven, ZInQ.Size.coefficient_lt_tower_eight
---

# Comparison with the towers

Let $2\uparrow\uparrow0=1$ and $2\uparrow\uparrow(n+1)=2^{2\uparrow\uparrow n}$, so $2\uparrow\uparrow1=2$ and
$2\uparrow\uparrow4=65536$. For every natural number $T<2^{2^{2^{9013}}}$,
$$(T+1)^{2048}<2^{2^{2^{9014}}}<2\uparrow\uparrow7\qquad\text{and}\qquad
2^{(T+1)^{2048}}<2\uparrow\uparrow8 .$$

**Proof sketch.** $T+1\le U=2^{2^{2^{9013}}}$, so
$(T+1)^{2048}\le U^{2048}=2^{2^{2^{9013}}\cdot2^{11}}=2^{2^{2^{9013}+11}}$, and
$2^{9013}+11<2^{9014}$; thus $(T+1)^{2048}<2^{2^{2^{9014}}}$. Next $2\uparrow\uparrow7=2^{2^{2^{2\uparrow\uparrow4}}}=2^{2^{2^{65536}}}$,
and $9014<65536$ with strict monotonicity of $k\mapsto2^{2^{2^k}}$ gives the first chain. The
second follows by applying $k\mapsto2^k$: $2^{(T+1)^{2048}}<2^{2\uparrow\uparrow7}=2\uparrow\uparrow8$. Only
monotonicity of exponentiation and the value $2\uparrow\uparrow4=65536$ are used.

## Depends on

None.

## Sources

- [Section 12.1 final comparison](../../../sources/size-locators.md#section-121-final-comparison)
