---
article_id: af_ea8693e192956863703c6806
declaration: def
origin: cited
---

# Lowering to a primitive program

The lowering $\operatorname{lower}(S)$ of a structured register program $S$ is the primitive register
program in final-halt form obtained by laying out one block of primitive instructions per
statement, by structural recursion, followed by a cleanup block, a rejection self-loop and the
final halt. Registers $\ge N_S$ are auxiliary; one of them, $z$, is reserved, never written,
and serves for unconditional jumps $\mathrm{decb}(z,k,k)$. Each block uses fresh auxiliary
registers, which are zero on entry and on exit.

- $r:=0$ is the loop $\mathrm{decb}(r,\cdot,\cdot)$ back to itself until $r$ is zero;
  $r:=r+1$ is $\mathrm{inc}(r,\cdot)$; $r:=r\mathbin{\dot-}1$ is $\mathrm{decb}(r,\cdot,\cdot)$ with both
  targets the next block.
- $r:=r'$ empties $r'$ into two auxiliary registers $a_1,a_2$, moves $a_1$ back into $r'$, then
  clears $r$ and moves $a_2$ into $r$; so a copy restores its source, and for $r=r'$ the block
  leaves $r$ unchanged (clearing $r$ before restoring $r'$ would double it). $r:=r'+r''$ first
  copies both operands into auxiliary registers (a snapshot, so aliasing is harmless), clears
  $r$ and moves both copies into $r$.
- $r:=r'\mathbin{\dot-}r''$ copies the operands, decrements both copies together until the copy
  of $r''$ is zero, using saturating decrement, then clears $r$ and moves the remaining copy of
  $r'$ into $r$; $r:=r'\cdot r''$ adds a copy of $r'$ (restored after each addition) to a fresh
  accumulator, counted down from a copy of $r''$, then clears $r$ and moves the accumulator into
  $r$. In every primitive block the destination is written only after all sources have been
  copied, which realizes the old-registers semantics even when a destination is a source.
- $(q,m):=\operatorname{divmod}(r',r'')$ jumps to the rejection loop if $r''$ is zero; otherwise it
  keeps $x=q\,y+\text{rem}$ for copies $x$ of $r'$ and $y$ of $r''$, subtracting $y$ from the
  remainder and incrementing $q$ only while $\text{rem}\ge y$.
- Tests are realized by a preserving test (decrement, restore, branch) or by comparing
  copies; $\mathbf{while}$ jumps back to its test after the body.
- $\mathbf{accept}$ jumps to the cleanup block, which clears every register below the total
  register count and then enters the final halt; $\mathbf{reject}$, and the end of $S$, jump to
  the rejection self-loop $\mathrm{decb}(z,k,k)$ at its own state $k$.

The layout assigns consecutive states to blocks and relocates every target accordingly. This
is a definition.

## Depends on

- [Structured register programs](structured-programs.md)
- [Primitive register programs](register-programs.md)

## Sources

- [Section 10.3 lowering](../../../../sources/compiler-translation-locators.md#section-103-lowering)
- [Section 10.3 interpreter](../../../../sources/compiler-translation-locators.md#section-103-interpreter)
- [Machine artifacts](../../../../sources/compiler-translation-locators.md#machine-artifacts)
