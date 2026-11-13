---
article_id: af_686e52cfd74872a5f7752985
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.IR.Op, ZInQ.Compiler.IR.Stmt, ZInQ.Compiler.IR.Outcome, ZInQ.Compiler.IR.BigStep, ZInQ.Compiler.IR.BigStep.deterministic, ZInQ.Compiler.IR.Program, ZInQ.Compiler.IR.Program.WF, ZInQ.Compiler.IR.Program.Accepts, ZInQ.Compiler.IR.Program.Total
---

# The ideal register language

The *ideal register language* has registers indexed by $\mathbb N$ holding natural numbers.
Its statements are:

- assignments $x\leftarrow k$ (a natural constant), $x\leftarrow y$, $x\leftarrow y+z$,
  $x\leftarrow y\mathbin{\dot-}z$ (truncated subtraction), $x\leftarrow y\cdot z$,
  $x\leftarrow\lfloor y/z\rfloor$ and $x\leftarrow y\bmod z$ (with $\lfloor y/0\rfloor=0$ and
  $y\bmod0=y$), where $x,y,z$ are registers that may coincide;
- sequencing $S_1;S_2$, the conditionals $\mathbf{if}\ y<z\ \mathbf{then}\ S_1\
  \mathbf{else}\ S_2$ and $\mathbf{if}\ y=z\ \mathbf{then}\ S_1\ \mathbf{else}\ S_2$, the loop
  $\mathbf{while}\ y<z\ \mathbf{do}\ S$, and the terminal statements $\mathbf{accept}$ and
  $\mathbf{reject}$.

The big-step semantics is the inductive relation $\langle S,\rho\rangle\Downarrow o$ between a
statement, a register file and an outcome $o\in\{\mathrm{normal}(\rho'),\mathrm{accept},\mathrm{reject}\}$,
with the usual rules (assignments update one register with the exact value; a terminal
outcome of $S_1$ skips $S_2$; a loop iterates while its test holds). A derivation exists
only for terminating executions. A program is a statement $S$ with a register bound
$\rho_S$ (all registers occurring in $S$ are below $\rho_S$) and $k\le\rho_S$ input registers; it
*accepts* $a\in\mathbb N^k$ if $\langle S,\rho_0(a)\rangle\Downarrow\mathrm{accept}$ for the initial
file $\rho_0(a)$ (inputs in registers $0,\dots,k-1$, all others $0$), and it is *total* if
for every $a$ some outcome is derivable. The language is deterministic: each statement
and file have at most one outcome.

This is a definition. It is the ideal intermediate representation of the manuscript (S22):
correctness is a statement about this ideal semantics, not about a budgeted simulator.

## Depends on

None.

## Sources

- [Section 10 reference program and IR](../../../../sources/compiler-natural-locators.md#section-10-reference-program-and-ir)
- [Section 10.3 lowering](../../../../sources/compiler-natural-locators.md#section-103-lowering)
- [Appendix B sources](../../../../sources/compiler-natural-locators.md#appendix-b-sources)
