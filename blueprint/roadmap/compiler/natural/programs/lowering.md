---
article_id: af_1f273c6614739f889af6af77
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.IR.assignB, ZInQ.Compiler.IR.ltTest, ZInQ.Compiler.IR.eqTest, ZInQ.Compiler.IR.code, ZInQ.Compiler.IR.Stmt.len, ZInQ.Compiler.IR.code_length, ZInQ.Compiler.IR.cleanup, ZInQ.Compiler.IR.lower, ZInQ.Compiler.IR.lower_length, ZInQ.Compiler.IR.lower_valid
---

# Lowering to primitive programs

For a program $S$ of the ideal register language with register bound $\rho_S$, the
*lowering* $\mathrm{low}(S)$ is the primitive program built as follows.

1. *Layout.* Registers below $\rho_S$ keep their meaning; register $J=\rho_S$ is the
   reserved jump register (always $0$ at block boundaries, so $\mathrm{dec}(J,x,x)$ is an
   unconditional jump to $x$); the six registers $J+1,\dots,J+6$ are auxiliary registers
   shared by all primitive blocks, each block starting and ending with them zero.
2. *Primitive blocks.* Every block for an assignment to $x$ first *snapshots* each source
   $y$: it moves $y$ into two fresh auxiliary registers $a,a'$ (decrement $y$, increment $a$
   and $a'$, until $y=0$) and moves $a$ back into $y$, so that $y$ is restored and $a'$
   holds its value. Only after all sources are snapshot is $x$ cleared (a loop of
   decrements) and written; hence aliasing of $x$ with $y$ or $z$, and $y=z$, are safe.
   Then: $x\leftarrow k$ increments $x$ $k$ times; $x\leftarrow y$ and $x\leftarrow y+z$
   move the snapshots into $x$; $x\leftarrow y\mathbin{\dot-}z$ moves the snapshot of $y$ into
   $x$ and then, once per unit of the snapshot of $z$, decrements $x$ if it is positive
   (saturating decrement); $x\leftarrow y\cdot z$ adds the snapshot of $y$ into $x$ (restoring
   it through a further auxiliary register) once per unit of the snapshot of $z$, then clears
   the snapshot of $y$; $x\leftarrow\lfloor y/z\rfloor$ and $x\leftarrow y\bmod z$ test the
   snapshot of $z$ for zero (giving $0$, respectively the snapshot of $y$) and otherwise move
   the snapshot $r$ of $y$ one unit at a time into a counter $m$, keeping a quotient $q$ and a
   register $c=z-m\ge1$: each unit decrements $c$, and when $c$ reaches $0$ the counter $m$ is
   cleared, $q$ is incremented and $c$ is refilled with $z$. This maintains $y=r+qz+m$ with
   $0\le m<z$, so at exit ($r=0$) $q=\lfloor y/z\rfloor$ and $m=y\bmod z$, and $q$ or $m$ is
   moved into $x$. Every block ends with its auxiliary registers zero and
   every register below $\rho_S$ other than $x$ unchanged.
3. *Control.* Sequencing concatenates blocks; a test $y<z$ or $y=z$ is a comparison loop
   on snapshots of $y$ and $z$ that branches directly to the two targets; a loop jumps back
   to its test.
4. *Termination.* $\mathbf{accept}$ jumps to a final *cleanup* stage that clears every
   register used by the program and then reaches the final halt; $\mathbf{reject}$ and normal
   completion of $S$ jump to a permanent self-loop $\mathrm{dec}(J,i,i)$ at its own state $i$.

Items 1-3 produce the *open code* $\mathrm{code}(S)$ of a statement, a list of instructions
with one entry state and one *normal exit* (the state after its last block), parameterized
by its start state; item 4 closes it into the primitive program $\mathrm{low}(S)$, valid for
its register count $r=J+7$, with all targets absolute.

This is a definition. The manuscript's lowering (S22) is described only at this level; the
exact block layout is fixed by the Lean definition.

## Depends on

- [The ideal register language](structured-programs.md)
- [Register machines](register-machine.md)

## Sources

- [Section 10.3 lowering](../../../../sources/compiler-natural-locators.md#section-103-lowering)
- [Section 10.3 interpreter](../../../../sources/compiler-natural-locators.md#section-103-interpreter)
