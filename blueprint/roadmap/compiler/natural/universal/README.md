---
article_id: af_02fccc89c41769dd575a610c
---

# The universal interpreter and the five-input circuit

Programs are numbered by $e+1=2^w(2D+1)$, with four base-$2^w$ digits of $D$ per state;
decoding is total. A valid primitive program has a code whose machine halts exactly when
the program does.

- [The universal program numbering](program-numbering.md)
- [Codes of primitive programs](program-numbering-encode.md)

The interpreter keeps the simulated registers in a tape list $\operatorname{cons}(h,t)=2^h(2t+1)$
and is assembled from arithmetic and list blocks. One loop iteration executes one decoded
instruction, and its all-zero halt is equivalent to virtual halting.

- [Tape lists](tape-lists.md)
- [Arithmetic blocks of the interpreter](interpreter-primitives.md)
- [List blocks of the interpreter](interpreter-list-primitives.md)
- [The universal interpreter](universal-interpreter.md)
- [One interpreter loop simulates one instruction](interpreter-step.md)
- [Correctness of the universal interpreter](interpreter-correct.md)

The shape of the explicit interpreter, including the structure of its cleanup stage, is a
finite check.

- [Shape of the universal interpreter](interpreter-shape.md)

Compiling the interpreter gives the universal halting circuit, with natural zeros exactly at
the halting pairs. Its numbers of variables and calls follow from the shape by the counting
statement of the packed construction; its node statistics, and those of the power template,
are a finite check on the two explicit constructions.

- [The universal halting circuit](halting-polynomial.md)
- [Counts of the universal halting circuit](halting-circuit-counts.md)
- [Node statistics of the halting circuit and the power template](halting-node-check.md)
- [Exact node statistics of the halting circuit](halting-node-exact.md)
- [Semantics of the universal halting circuit](halting-polynomial-semantics.md)

The five-input circuit fixes the program input to the wrapper's code, moves the packed input
to variable five, shifts the other variables by seven, and adds the four squared pairing
equations. The program literal is bounded, from a finite check on the size of the wrapper,
without being evaluated; the shape of the five-input circuit then follows.

- [Size of the wrapper](wrapper-size-check.md)
- [Size of the program literal](wrapper-code-size.md)
- [The five-input natural precision circuit](precision-circuit.md)
- [The precision circuit is a specialization](precision-circuit-specialization.md)
- [Shape of the natural precision circuit](circuit-node-counts.md)
