---
article_id: af_a953b1858d9587fbbbcb9abb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.IR.jdblCode, ZInQ.Compiler.IR.jdblBCode, ZInQ.Compiler.IR.jaddBCode, ZInQ.Compiler.IR.jmulCode, ZInQ.Compiler.IR.jdblCode_spec, ZInQ.Compiler.IR.jdblBCode_spec, ZInQ.Compiler.IR.jaddBCode_spec, ZInQ.Compiler.IR.jmulCode_spec
---

# Point routines

A Jacobian triple $(X,Y,Z)\in\mathbb Z[s]^3$ is represented by three field representations
in six consecutive integer variables (twelve registers). There are statements over integer
variables (compiled into the ideal register language by the signed integer routines),
using temporaries from a base $T$ on, computing: the constant triples $P^{\rm J}_0$ and
$O=(1,1,0)$; the plain Jacobian doubling; the branching addition $\oplus$ and the doubling
$\mathrm{dbl}^\ast$ of the scalar-multiplication statement, including the cases $Z=0$, equal
abscissas ($H=0$) with equal or opposite ordinates, and zero ordinate; and the halving loop
computing $\mathrm{mul}(k)$ for an integer variable $k$ (negating $Y$ at the end when $k<0$).
Each, started with its operand and result triples (and $k$) below $T$, and, for the
addition, the result triple equal to or disjoint from each operand triple, terminates
normally with the exact triple of the Jacobian formulas in the result triple and every
variable below $T$ outside the result triple unchanged; the halving loop terminates
because its counter halves.

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
