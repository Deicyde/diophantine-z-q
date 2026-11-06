---
article_id: af_a953b1858d9587fbbbcb9abb
declaration: theorem
origin: cited
---

# Point routines

A Jacobian triple $(X,Y,Z)\in\mathbb Z[s]^3$ is represented by three field representations
(twelve registers). There are statements of the ideal register language computing:
the constant triple $P^{\rm J}_0$ and $O=(1,1,0)$; negation; the branching addition $\oplus$
and the doubling $\mathrm{dbl}^\ast$ of the scalar-multiplication statement, including the
cases $Z=0$, equal abscissas ($H=0$) with equal or opposite ordinates, and zero ordinate;
and the halving loop computing $\mathrm{mul}(k)$ for a signed integer $k$. Each, started
with operands represented and temporaries distinct, terminates normally with the exact
triple of the Jacobian formulas represented and every other register unchanged; the
halving loop terminates because its counter halves.

**Proof sketch.** Straight-line compositions of the field routines implementing the
displayed formulas, with branches on the zero tests of $Z_1$, $Z_2$, $H$, $\Lambda$, $Y$; the
loop is verified with the invariant of the scalar-multiplication statement, the measure
being the counter.

## Depends on

- [Quadratic-field routines](ir-field-routines.md)
- [Scalar multiplication by halving](../precision/jacobian-scalar-multiplication.md)

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
- [Section 10 reference program and IR](../../../../sources/compiler-natural-locators.md#section-10-reference-program-and-ir)
