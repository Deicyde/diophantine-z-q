---
article_id: af_1f273c6614739f889af6af77
declaration: def
origin: cited
---

# Lowering to primitive programs

For a program $S$ of the ideal register language with register bound $\rho_S$, the
*lowering* $\mathrm{low}(S)$ is the primitive program built as follows.

1. *Layout.* Registers below $\rho_S$ keep their meaning; register $J=\rho_S$ is the
   reserved jump register (always $0$ at block boundaries, so $\mathrm{dec}(J,x,x)$ is an
   unconditional jump to $x$); registers above $J$ are fresh auxiliary registers, each
   primitive block using its own registers (or registers it clears before use).
2. *Primitive blocks.* $x\leftarrow k$: clear $x$ (a loop of decrements) and increment it $k$
   times. $x\leftarrow y$ and $x\leftarrow y+z$: snapshot the sources into fresh registers
   by moving them into two auxiliary registers and restoring them (so aliasing of $x$ with
   $y$ or $z$ is safe), then add by repeated increment. $x\leftarrow y\mathbin{\dot-}z$: copy $y$,
   then decrement it once per unit of a copy of $z$ (saturating decrement).
   $x\leftarrow y\cdot z$: repeated addition. $x\leftarrow\lfloor y/z\rfloor$,
   $x\leftarrow y\bmod z$: test $z=0$ first; otherwise subtract copies of $z$ from a copy of
   $y$ while the remainder is at least $z$, maintaining $y=qz+r$. Every block ends with its
   auxiliary registers zero and every register below $\rho_S$ other than $x$ unchanged.
3. *Control.* Sequencing concatenates blocks; a test $y<z$ or $y=z$ is a block computing
   the comparison into an auxiliary register followed by a decrement branch on it; a loop
   jumps back to its test.
4. *Termination.* $\mathbf{accept}$ jumps to a final *cleanup* stage that clears every
   register used by the program and then reaches the final halt; $\mathbf{reject}$ and normal
   completion of $S$ jump to a permanent self-loop $\mathrm{dec}(J,i,i)$ at its own state $i$.

Items 1-3 produce the *open code* $\mathrm{code}(S)$ of a statement, a list of instructions
with one entry state and one *normal exit* (the state after its last block), parameterized
by its start state and by the first free auxiliary register; item 4 closes it into the
primitive program $\mathrm{low}(S)$, valid for its register count $r$ (the maximum auxiliary
register plus one), with all targets absolute.

This is a definition. The manuscript's lowering (S22) is described only at this level; the
exact block layout is fixed by the Lean definition.

## Depends on

- [The ideal register language](structured-programs.md)
- [Register machines](register-machine.md)

## Sources

- [Section 10.3 lowering](../../../../sources/compiler-natural-locators.md#section-103-lowering)
- [Section 10.3 interpreter](../../../../sources/compiler-natural-locators.md#section-103-interpreter)
