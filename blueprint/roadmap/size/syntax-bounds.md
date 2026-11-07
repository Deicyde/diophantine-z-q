---
article_id: af_59ef7ca67a1fe0dbf4f25ea2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.Pstar_size, ZInQ.Size.Pstar_target_bounds
---

# Variable, degree and coefficient bounds

Assume the catalogue bound. The specified polynomial
$$P_*\in\mathbb Z[X_0,X_1,\dots,X_{292890231904}]$$
has $292{,}890{,}231{,}905$ variables (the input $X_0$ and $292{,}890{,}231{,}904$ witnesses), total
degree
$$\deg P_*\le(T+1)^{2048}<2\uparrow\uparrow7,$$
and every coefficient satisfies
$$|[X^\alpha]P_*|\le2^{(T+1)^{2048}}<2\uparrow\uparrow8,$$
where $2\uparrow\uparrow0=1$ and $2\uparrow\uparrow(n+1)=2^{2\uparrow\uparrow n}$.

This is the quantitative part of input B. The constants $T$ and $D$ are never evaluated.

**Proof sketch.** The variable count is the witness accounting of the specification
chapter. The degree and coefficient bounds in terms of $T$ come from the syntax-height
induction at root height $256$ with $B=T+1$, and the literal cutoff gives
$T<2^{2^{2^{9013}}}$, so the tower comparison applies.

## Depends on

- [The specified polynomial](../syntax/literal-polynomial.md)
- [The prescribed fixed constants](../syntax/constants/fixed-constants.md)
- [The catalogue bound](../main/catalogue-bound.md)

## Proof depends on

- [Witness accounting of the specified polynomial](../syntax/recipes/witness-accounting.md)
- [Degree and coefficient bounds for the specified polynomial](majorants/degree-coefficient-bound.md)
- [The literal cutoff](cutoff.md)
- [Comparison with the towers](majorants/tower-comparison.md)

## Sources

- [Section 12.1 syntax heights](../../sources/size-locators.md#section-121-syntax-heights)
- [Section 12.1 final comparison](../../sources/size-locators.md#section-121-final-comparison)
- [Section 12.1 checked facts](../../sources/size-locators.md#section-121-checked-facts)
