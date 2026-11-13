---
article_id: af_2b2e723387ed825e28336723
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.IR.satCode, ZInQ.Compiler.IR.cmulCode, ZInQ.Compiler.IR.cpowCode, ZInQ.Compiler.IR.cfactCode, ZInQ.Compiler.IR.caddCode, ZInQ.Compiler.IR.cmaxCode, ZInQ.Compiler.IR.cA0Code, ZInQ.Compiler.IR.cBoundCode, ZInQ.Compiler.IR.divFourCode, ZInQ.Compiler.IR.cA0Code_spec, ZInQ.Compiler.IR.cBoundCode_spec
---

# Capped arithmetic routines

Fix an integer variable holding a cap $L$ (in the precision program $L\ge1$). There are
statements over integer variables (compiled into the ideal register language by the
signed integer routines), using temporaries from a base $T$ on, computing on natural
operands the saturation $\sigma_L(x)=\min(x,L+1)$, the saturated sum $\sigma_L(x+y)$, the
capped product $\mathrm{cmul}_L$, the saturated maximum, the capped power $\mathrm{cpow}_L(x,e)$
(a loop of $e$ capped multiplications), the saturated factorial $\sigma_L(n!)$ (a loop of $n$
capped multiplications), the capped value $\langle e_A\rangle_L$ of the precision height
constant, the capped bound $\beta$ of the capped precision test, and the division-by-four
loop $x\mapsto\lfloor x/4\rfloor$ repeated $\beta$ times. Each, started with its operands, the
cap and the result below $T$ (for the division loop, $x\ne\beta$), terminates normally with
the value prescribed by the corresponding mathematical definition in the result and every
variable below $T$ other than the result unchanged.

**Proof sketch.** Each statement is a direct transcription of its definition; loops are
verified by their invariants (the power loop by $\sigma_L(x^i)$ after $i$ steps, the factorial
loop by induction on the counter, the division loop by $x_i=\lfloor x/4^i\rfloor$), with
termination by the increasing counter, which stops at the exponent, at $n$ and at $\beta$
respectively.

## Depends on

- [The ideal register language](structured-programs.md)
- [Capped multiplication and binary exponentiation](../precision/capped-power.md)
- [The capped precision test](../precision/capped-height-test.md)

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
- [Section 10 saturation](../../../../sources/compiler-natural-locators.md#section-10-saturation)
