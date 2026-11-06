# Interpreter, lowering and five-input specialization

This section proves the machine half of equation (C.4): the universal interpreter, run on the
program literal $c_3$ and a Cantor code of five naturals, accepts exactly when the precision
predicate holds. Together with the natural chapter's compilation of the interpreter into the
universal halting polynomial and the five-input specialization below, this gives (C.4). None of
it uses a height, restricted-converse or rational-model premise.

## Programs and their numbering

The machines are increment/decrement/branch programs on natural registers. Acceptance in the
sense of the packed-history compiler means reaching the unique final halt with all registers
zero; halting anywhere, with any registers, is virtual halting.

- [Primitive register programs](register-programs.md)

The universal numbering writes $e+1=2^w(2D+1)$ and reads opcode, register and two targets of
state $p$ from the base-$2^w$ digits of $D$ at positions $4p,\dots,4p+3$. Missing digits are
zero, so decoding is total, and every finite program is decoded from its code.

- [The universal program numbering](program-numbering.md)
- [Decoding a program code](program-numbering-decode.md)

## Structured programs and lowering

Both the interpreter and the precision computation are written as structured register
programs: primitive assignments (including natural subtraction, multiplication and guarded
division), tests, loops, acceptance and rejection, with a big-step semantics.

- [Structured register programs](structured-programs.md)

The lowering lays out one block of primitive instructions per statement, with fresh auxiliary
registers that are zero at block boundaries, snapshots of overlapping sources, a reserved zero
register for jumps, a cleanup block entered on acceptance and a permanent self-loop entered on
rejection.

- [Lowering to a primitive program](lowering.md)

By induction on derivations and on completed loop iterations, the lowered machine halts
exactly when the structured program accepts, and then with all registers zero; rejection and
divergence both give a run that never halts, although the precision program itself is total.

- [The lowered machine halts exactly on acceptance](lowering-correctness.md)

## The universal interpreter

The interpreter keeps the simulated registers in a list code built from
$\operatorname{cons}(h,t)=2^h(2t+1)$, decoded by repeated halving and updated through a saved
reversed prefix; absent entries read as zero.

- [List codes for the interpreter tape](list-codes.md)
- [The universal interpreter](universal-interpreter.md)

One iteration of its main loop executes exactly one decoded instruction with finite work. A
simulated halt is an acceptance, hence enters the cleanup of the lowering, while an infinite
simulation never enters it; so the all-zero halt of the interpreter is equivalent to virtual
halting of the simulated program.

- [One interpreter loop is one decoded step](interpreter-step.md)
- [Correctness of the universal interpreter](interpreter-correctness.md)

## The precision program

The precision predicate decodes the five inputs in the order $(n,\kappa,a,l,j)$, rejects early
unless $n\notin\mathcal C$, $\kappa\ne0$, $a,l\ge1$, $j=na$, and then applies two strict tests to
the exactly computable rationals $r(a,j)$ and $\epsilon_l$. The constant $A^{(0)}_{\rm ht}$ in the
second test is astronomically large and is never evaluated.

- [The precision predicate](precision-predicate.md)
- [Nonzero multiples of the generator are nondegenerate](nondegenerate-multiples.md)

The precision program computes in normalized signed pairs and in pairs over $1,\sqrt2$. Norm
zero decides vanishing, so every division can be guarded exactly; the Jacobian formulas
represent the group law, with equal abscissas split into doubling and opposite points; and
capped arithmetic computes $\min(x,L+1)$ of the fixed height expression, so the second test is
decided at the precision actually available.

- [Norm zero implies zero](quadratic-norm-zero.md)
- [Jacobian formulas for the group law](jacobian-formulas.md)
- [The fixed Jacobian triple of the generator](projective-generator.md)
- [Capped arithmetic](capped-arithmetic.md)
- [The precision program](precision-ir.md)
- [The precision program computes the precision predicate](ir-correctness.md)

## The wrapper and the specialization

The wrapper inverts four Cantor pairs, puts the five codes into registers $0$ to $4$ with its
scratch above the precision machine's registers, and jumps into the relocated precision
machine. Its code is the program literal $c_3$.

- [Cantor pairing and unpairing](cantor-unpairing.md)
- [The wrapper and the program literal](wrapper.md)
- [Correctness of the wrapper](wrapper-correctness.md)

Chaining the interpreter, the numbering, the wrapper, the lowering and the precision program
gives the machine statement.

- [The universal interpreter at the program literal](precision-machine-semantics.md)

The polynomial specialization fixes the program input of the universal halting polynomial to
$c_3$, moves the packed input to variable five and every other old variable by seven, and adds
the four squared pairing equations, which force their unique Cantor values. Applied to the
natural chapter's universal halting polynomial, its semantics and the machine statement give
(C.4).

- [The five-input specialization](five-input-specialization.md)
- [Semantics of the five-input specialization](specialization-semantics.md)
