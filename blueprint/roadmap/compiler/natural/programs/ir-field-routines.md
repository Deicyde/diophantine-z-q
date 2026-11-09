---
article_id: af_ea552c7c4f84feb0d25907e0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.IR.FExpr, ZInQ.Compiler.IR.FExpr.code, ZInQ.Compiler.IR.fMul, ZInQ.Compiler.IR.IExpr, ZInQ.Compiler.IR.zeroFlag, ZInQ.Compiler.IR.guardNonzero, ZInQ.Compiler.IR.intConst, ZInQ.Compiler.IR.fMul_spec, ZInQ.Compiler.IR.FExpr.code_spec, ZInQ.Compiler.IR.IExpr.code_spec, ZInQ.Compiler.IR.zeroFlag_spec, ZInQ.Compiler.IR.guardNonzero_spec, ZInQ.Compiler.IR.intConst_spec
---

# Quadratic-field routines

An element $\alpha=g+hs\in\mathbb Z[s]$ is *represented* by two consecutive integer variables
holding $g$ and $h$ (two signed integer pairs, four registers). There are statements over
integer variables (compiled into the ideal register language by the signed integer
routines), using temporaries from a base $T$ on, that compute:

- the value, into a result pair, of every *field expression* built from pairs, integer
  variables (as $g+0s$), constants of $\mathbb Z[s]$, addition, subtraction, negation,
  multiplication $(g+hs)(g'+h's)=(gg'+2hh')+(gh'+hg')s$ and conjugation $g+hs\mapsto g-hs$
  (in particular multiplication by an integer);
- the value, into a result variable, of every *integer expression* built from integer
  variables, integer constants, addition, subtraction, multiplication, negation and
  absolute value (in particular the norm $\operatorname N(g+hs)=g^2-2h^2$ and the rational
  component $g$);
- an integer constant (by Horner's rule in base $64$);
- the flag $[\alpha=0]$, and a guard that executes $\mathbf{reject}$ when $\alpha=0$.

If the variables of the expression and the result lie below $T$ (for the direct code of a
field expression, all variables of the expression lie below the result pair; for a single
product of two pairs, the result pair is disjoint from both operands), the statement
terminates normally with the exact value in the result, and every variable below $T$
other than the result is unchanged. Likewise the flag, in a variable distinct from $T$ and
from the pair, with $T$ outside the pair, is computed exactly, changing only the flag and
$T$. The guard on a pair
below $T$ executes $\mathbf{reject}$ if $\alpha=0$, and otherwise terminates normally changing
only $T$ and $T+1$.

**Proof sketch.** Compositions of the integer operations, verified componentwise and by
induction on the expression; an operand that is not a variable is first evaluated into its
own slot of temporaries.

## Depends on

- [Signed integer routines](ir-integer-routines.md)
- [The field $K_0=\mathbb Q(\sqrt2)$](../../../model/field/quadratic-field.md)

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
