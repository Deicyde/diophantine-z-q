---
article_id: af_9224e7100caa646cdb5a15d2
declaration: lemma
origin: cited
---

# The fixed Jacobian triple of the generator

Let $A=-d^2=-11243+7950s$ and let
$$X_0=3282-2320s,\qquad Y_0=-247440+174966s,\qquad Z_0=4,$$
that is, $(X_0,Y_0,Z_0)=\bigl(2(1641-1160s),\ 2(-123720+87483s),\ 4\bigr)\in\mathbb Z[s]^3$. Then

1. $Y_0^2=X_0^3+AX_0Z_0^4$; explicitly both sides equal $122452755912-86587174080\,s$;
2. $X_0/Z_0^2=(1641-1160s)/8$ and $Y_0/Z_0^3=(-123720+87483s)/32$, so the triple represents the
   affine point $P_0$, and $Z_0\ne0$, $X_0\ne0$, $Y_0\ne0$.

This is the manuscript's remark that the fixed projective point is the same affine $P_0$. It
is a closed statement about six explicit integers: compute in $\mathbb Z[s]$ with
$(a+bs)(a'+b's)=(aa'+2bb')+(ab'+a'b)s$. Item 1 also follows from the curve equation for $P_0$
multiplied by $Z_0^6=4096$, and $d^2=(75-53s)^2=11243-7950s$.

## Depends on

- [The point $P_0$](../../../model/field/generator-point.md)
- [Jacobian formulas for the group law](jacobian-formulas.md)

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-translation-locators.md#section-103-precision-ir)
