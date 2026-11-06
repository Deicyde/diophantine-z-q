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
- [Shape of the universal interpreter](interpreter-shape.md)

Compiling the interpreter gives the universal halting circuit, with natural zeros exactly at
the halting pairs.

- [The universal halting circuit](halting-polynomial.md)
- [Semantics of the universal halting circuit](halting-polynomial-semantics.md)

The five-input circuit fixes the program input to the wrapper's code, moves the packed input
to variable five, shifts the other variables by seven, and adds the four squared pairing
equations. The program literal is bounded without being evaluated, and the node statistics
of the circuits are finite checks.

- [Size of the program literal](wrapper-code-size.md)
- [The five-input natural precision circuit](precision-circuit.md)
- [The precision circuit is a specialization](precision-circuit-specialization.md)
- [Node statistics of the compiled circuits](circuit-node-counts.md)
