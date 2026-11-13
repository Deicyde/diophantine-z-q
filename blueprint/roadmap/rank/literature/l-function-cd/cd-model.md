---
article_id: af_9aebf643fde94402441656fa
declaration: def
origin: background
statement: formalized
lean: ZInQ.Literature.cdModel, ZInQ.Literature.cdModel_Δ, ZInQ.Literature.cdModel_c₄, ZInQ.Literature.cdModel_map, ZInQ.Literature.cdModel_eq_shortCurve
---

# The model $y^2=x^3-d^2x$ over a ring

For a commutative ring $S$ and a natural number $d$, the *model $y^2=x^3-d^2x$ over $S$* is the
Weierstrass equation with coefficients
$$a_1=a_2=a_3=a_6=0,\qquad a_4=-d^2$$
in $S$. Its invariants are
$$\Delta=(2d)^6=64d^6,\qquad c_4=48d^2,$$
the integers $(2d)^6$ and $48d^2$ read in $S$. For a ring homomorphism $S\to S'$, applying it to
the coefficients gives the model $y^2=x^3-d^2x$ over $S'$. Over a field $F$ the model is the short
Weierstrass curve $y^2=x^3+Ax$ with $A=-d^2$; over $\mathbb Q$ it is the curve $C_d$.

**Proof sketch** (of the basic facts). Substitute $a_1=a_2=a_3=a_6=0$, $a_4=-d^2$ into the formulas
for $b_2,b_4,b_6,b_8$: $b_2=b_6=0$, $b_4=-2d^2$, $b_8=-d^4$, so $c_4=b_2^2-24b_4=48d^2$ and
$\Delta=-8b_4^3=64d^6$. A ring homomorphism fixes $0$ and maps $-d^2$ to $-d^2$.

## Depends on

None.

## Sources

- [The L-series of an elliptic curve](../../../../sources/rank-locators.md#the-l-series-of-an-elliptic-curve)
- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
