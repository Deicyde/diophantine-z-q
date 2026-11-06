---
article_id: af_32b090fd87327c45949fffc4
declaration: lemma
origin: cited
---

# Jacobian formulas for the group law

Let $K$ be a field of characteristic different from $2$ and $A\in K$, and consider
$y^2=x^3+Ax$ in Jacobian coordinates: a triple $(X,Y,Z)$ with $Z\ne0$ and
$Y^2=X^3+AXZ^4$ represents the affine point $(X/Z^2,Y/Z^3)$, and a triple with $Z=0$ represents
the identity.

1. *Doubling.* Let $Z\ne0$. If $Y=0$ the represented point has order dividing $2$ and its double
   is $O$. If $Y\ne0$ put $S=4XY^2$, $M=3X^2+AZ^4$ and
   $$X'=M^2-2S,\qquad Y'=M(S-X')-8Y^4,\qquad Z'=2YZ .$$
   Then $Z'\ne0$, $Y'^2=X'^3+AX'Z'^4$, and $(X',Y',Z')$ represents the double, given affinely by
   the tangent slope $\lambda=(3x^2+A)/(2y)$.
2. *Addition.* Let $Z_1,Z_2\ne0$ and put $U_1=X_1Z_2^2$, $U_2=X_2Z_1^2$, $S_1=Y_1Z_2^3$,
   $S_2=Y_2Z_1^3$. If $U_1\ne U_2$, put $H=U_2-U_1$, $R=S_2-S_1$ and
   $$X_3=R^2-H^3-2U_1H^2,\qquad Y_3=R(U_1H^2-X_3)-S_1H^3,\qquad Z_3=HZ_1Z_2 ;$$
   then $Z_3\ne0$, $(X_3,Y_3,Z_3)$ lies on the curve and represents the sum, given affinely by
   the chord slope. If $U_1=U_2$ the abscissas are equal: $S_1=S_2$ means the points are equal
   (use doubling), and otherwise $S_1=-S_2\ne0$ and the sum is $O$: from the two curve
   equations, $S_i^2=U_i^3+AU_iZ_1^4Z_2^4$, so $U_1=U_2$ gives $S_1^2=S_2^2$.

Each statement is a polynomial identity in the coordinates after multiplying out the
denominators $Z^2$, $Z^3$, $2y$ and $x_2-x_1$, together with the field facts $Z\ne0$,
$Y\ne0$, $H\ne0$. They are independent of the generator theorem and use no property of any
particular point; the fixed starting triple of $P_0$ is a separate finite check.

**Proof sketch.** Substitute $x_i=X_i/Z_i^2$, $y_i=Y_i/Z_i^3$ into the affine chord and tangent
formulas and clear denominators; each resulting identity is checked by ring normalization
using the curve equations of the inputs.

## Depends on

None.

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-translation-locators.md#section-103-precision-ir)
- [Section 10 opening](../../../../sources/compiler-translation-locators.md#section-10-opening)
