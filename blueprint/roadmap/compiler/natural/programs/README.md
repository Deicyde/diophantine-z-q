---
article_id: af_a346cbae9b067b1218be2271
---

# Programs, lowering and the wrapper

Register machines have increment, decrement-or-branch and halt instructions. A primitive
program halts only at its last instruction; it accepts when it halts with every register
zero.

- [Register machines](register-machine.md)

The precision program is written in an ideal register language with natural arithmetic
and structured control, whose semantics is a statement about terminating executions, not
about a budgeted simulator. Lowering replaces each operation by a primitive block with
fresh auxiliary registers; acceptance enters cleanup and rejection a permanent self-loop.

- [The ideal register language](structured-programs.md)
- [Lowering to primitive programs](lowering.md)
- [Correctness of the lowering](lowering-correct.md)

The precision program is built from verified routines for normalized signed integers,
quadratic-field pairs, Jacobian points and capped arithmetic. It follows the decision
program step by step.

- [Signed integer routines](ir-integer-routines.md)
- [Quadratic-field routines](ir-field-routines.md)
- [Point routines](ir-point-routines.md)
- [Capped arithmetic routines](ir-capped-routines.md)
- [The precision program](precision-ir.md)
- [Correctness of the precision program](precision-ir-correct.md)
- [The precision machine halts exactly on acceptance](precision-machine.md)

The wrapper receives the five inputs as one Cantor code, inverts four pairs into registers
zero to four with scratch above the precision machine's registers, and runs the relocated
precision machine.

- [Cantor pairing and its decoder](cantor-pairing.md)
- [Unique Cantor unpairing](cantor-unpairing.md)
- [The wrapper program](wrapper-program.md)
- [Correctness of the wrapper](wrapper-correct.md)
