---
article_id: af_6a9944f2ba55f0469d6562f5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Precision.curveE_P0J, ZInQ.Compiler.Precision.P0J_affine, ZInQ.Compiler.Precision.rep_P0J
---

# The fixed Jacobian point

In $\mathbb Z[s]$, $s^2=2$, with $A=-11243+7950s$, the triple
$$(X_0,Y_0,Z_0)=(3282-2320s,\ -247440+174966s,\ 4)$$
satisfies $Y_0^2=X_0^3+AX_0Z_0^4$, and in $K_0$
$$\frac{X_0}{Z_0^2}=\frac{3282-2320s}{16}=\frac{1641-1160s}{8}=x(P_0),\qquad
\frac{Y_0}{Z_0^3}=\frac{-247440+174966s}{64}=\frac{-123720+87483s}{32}=y(P_0).$$
So the fixed projective point of the precision computation is the affine point $P_0$.

This is a finite computation on six explicit integers: both sides of the curve equation
equal $122452755912-86587174080s$, and the two quotients are the displayed coordinates of
$P_0$ ($3282=2\cdot1641$, $2320=2\cdot1160$, $247440=2\cdot123720$, $174966=2\cdot87483$,
$Z_0^2=16$, $Z_0^3=64$). It does not use the generator theorem.

## Depends on

- [The generator curve $E$](../../../model/field/generator-curve.md)
- [The point $P_0$](../../../model/field/generator-point.md)

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
