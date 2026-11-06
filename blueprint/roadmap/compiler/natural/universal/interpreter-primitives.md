---
article_id: af_af48125e8f15fd2be2c39f83
declaration: theorem
origin: cited
---

# Arithmetic blocks of the interpreter

The universal interpreter is assembled from primitive-program blocks, each with an entry
state, exit states, argument and result registers, and private scratch registers, using a
reserved jump register $J$ (register $2$ in the interpreter) that is zero at every block
boundary. For each of the following blocks, entered with $J=0$ and its scratch registers
zero, the run reaches an exit after finitely many steps with the stated effect, $J$ and
the scratch registers zero again, and every other register unchanged:

1. *clear* $x$: $x\leftarrow0$;
2. *preserving zero test* of $x$: exits to the zero or nonzero exit according to $x$,
   with $x$ unchanged (decrement and restore);
3. *copy* $x\leftarrow y$ ($x\ne y$): $y$ is restored through a scratch counter;
4. *addInto* $x\leftarrow x+y$, also when $x$ and $y$ are the same register (the operand is
   snapshot before $x$ is overwritten);
5. *ifLt* $y<z$: exits according to the comparison of private copies;
6. *divmod* with divisor $z\ge1$: $q\leftarrow\lfloor y/z\rfloor$, $r\leftarrow y\bmod z$, by
   repeated subtraction from a private remainder maintaining $y=qz+r$, subtracting only when
   $r\ge z$ (the interpreter's divisors are at least $2$);
7. *divmod2*: halving with parity, consuming pairs.

**Proof sketch.** Each block is a fixed short program; its correctness is a loop invariant
(the sum of the moved register and the counter is constant for copies and additions; $y=qz+r$
for division) and termination by a decreasing register.

## Depends on

- [Register machines](../programs/register-machine.md)

## Sources

- [Section 10.3 interpreter](../../../../sources/compiler-natural-locators.md#section-103-interpreter)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
