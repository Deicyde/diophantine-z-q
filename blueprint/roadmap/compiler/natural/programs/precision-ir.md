---
article_id: af_d8ae106ff8c664b959067cc1
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.IR.precisionZ, ZInQ.Compiler.IR.precisionProgram, ZInQ.Compiler.IR.precisionProgram_wf
---

# The precision program

The *precision program* $S_{\rm prec}$ is the program of the ideal register language with
$5$ inputs (the natural numbers $c_0,\dots,c_4$ in registers $0,\dots,4$) that performs the
steps of the exact decision program in order, using the routines: decode the five inputs
into signed pairs; perform the early tests and execute $\mathbf{reject}$ when one fails;
compute the three Jacobian representatives with the point routines and reject on a zero
third or second coordinate; form $\nu_k$, $N_k$, $U$, $V$, $\theta$, $\delta$ with the field
and signed routines and reject unless the closeness inequality holds; compute
$L=\lfloor(V-1)/(4U)\rfloor$, reject if $L=0$, compute $M=|\kappa F(n)|$, then $\beta$ with the
capped routines, run the division-by-four loop, and execute $\mathbf{accept}$ if its final
value is at least $1$ and $\mathbf{reject}$ otherwise. All other registers start at $0$;
the routines take their temporaries from a common region above all named quantities.

This is a definition. The manuscript's IR S22 is not available in this repository; this
program is specified from the description of S21 and S22 in Section 10, and its exact
register allocation is fixed by the Lean definition.

## Depends on

- [The ideal register language](structured-programs.md)
- [The exact decision program](../precision/decision-program.md)
- [Signed integer routines](ir-integer-routines.md)
- [Quadratic-field routines](ir-field-routines.md)
- [Point routines](ir-point-routines.md)
- [Capped arithmetic routines](ir-capped-routines.md)

## Sources

- [Section 10 reference program and IR](../../../../sources/compiler-natural-locators.md#section-10-reference-program-and-ir)
- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
- [Appendix B sources](../../../../sources/compiler-natural-locators.md#appendix-b-sources)
