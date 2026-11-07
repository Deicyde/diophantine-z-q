---
article_id: af_af48125e8f15fd2be2c39f83
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Universal.runs_clear, ZInQ.Compiler.Universal.compile_correct_in, ZInQ.Compiler.Universal.runs_copyBlock, ZInQ.Compiler.Universal.runs_addBlock, ZInQ.Compiler.Universal.runs_doubleBlock, ZInQ.Compiler.Universal.runs_divModBlock
---

# Arithmetic blocks of the interpreter

The universal interpreter is assembled from primitive-program blocks, each with an entry
state, exit states, argument and result registers, and private scratch registers, using a
reserved jump register $J$ (register $2$ in the interpreter) that is zero at every block
boundary. Each block clears its scratch registers before using them. For each of the
following blocks, entered with $J=0$ and arbitrary scratch values, the run reaches an exit
after finitely many steps with the stated effect on its result registers and $J=0$ again;
every register other than its results and scratch registers is unchanged, and the scratch
registers may be left nonzero:

1. *clear* $x$: $x\leftarrow0$;
2. *preserving zero test* of $x$: exits to the zero or nonzero exit according to $x$,
   with $x$ unchanged (decrement and restore);
3. *copy* $x\leftarrow y$ ($x\ne y$): $y$ is restored through a scratch counter;
4. *addInto* $x\leftarrow x+y$, also when $x$ and $y$ are the same register (the operand is
   snapshot before $x$ is overwritten);
5. *ifLt* $y<z$: a comparison loop that consumes both registers and exits according to
   whether $y<z$, leaving $y=0$, $z=z-y-1$ if $y<z$ and $y=y-z$, $z=0$ otherwise (callers
   compare private copies);
6. *divmod* with divisor $z\ge1$: $q\leftarrow\lfloor y/z\rfloor$, $r\leftarrow y\bmod z$, by
   repeated subtraction from a private remainder maintaining $y=qz+r$, subtracting only when
   $r\ge z$ (the interpreter's divisors are at least $2$);
7. *divmod2* of $y$ into $(q,r)$: $q\leftarrow q+\lfloor y/2\rfloor$, $r\leftarrow y\bmod2$ and
   $y\leftarrow0$ (halving with parity, consuming $y$ in pairs; callers clear $q$ first).

**Proof sketch.** Each block is a fixed short program; its correctness is a loop invariant
(the sum of the moved register and the counter is constant for copies and additions; $y=qz+r$
for division) and termination by a decreasing register.

## Depends on

- [Register machines](../programs/register-machine.md)

## Sources

- [Section 10.3 interpreter](../../../../sources/compiler-natural-locators.md#section-103-interpreter)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
