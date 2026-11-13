---
article_id: af_b260f69898a4964edbb06a6f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.IR.precisionZ_spec, ZInQ.Compiler.IR.precisionProgram_bigStep, ZInQ.Compiler.IR.precisionProgram_total, ZInQ.Compiler.IR.precisionProgram_correct, ZInQ.Compiler.IR.precisionProgram_accepts_iff
---

# Correctness of the precision program

The precision program is total, and for every $c\in\mathbb N^5$ it accepts $c$ if and only
if $\mathrm{decide}(c)=\mathrm{true}$, if and only if $\operatorname{accepts}(c)$. Its outcome on
an input that fails an early test is $\mathbf{reject}$.

**Proof sketch.** Compose the routine contracts along the program: after each routine the
registers represent exactly the quantities of the corresponding step of the decision
program, every branch agrees with the corresponding test, and every loop terminates (the
halving scalar loop, the bounded factorial and capped-power loops, and the division loop
of at most $L+1$ steps). Hence the derivable outcome is $\mathbf{accept}$ exactly when the
decision program returns true, and the correctness of the decision program gives the
relation.

## Depends on

- [The precision program](precision-ir.md)
- [The precision relation](../precision/precision-relation.md)

## Proof depends on

- [Signed integer routines](ir-integer-routines.md)
- [Quadratic-field routines](ir-field-routines.md)
- [Point routines](ir-point-routines.md)
- [Capped arithmetic routines](ir-capped-routines.md)
- [Correctness of the decision program](../precision/decision-program-correct.md)

## Sources

- [Section 10 reference program and IR](../../../../sources/compiler-natural-locators.md#section-10-reference-program-and-ir)
- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
