---
article_id: af_fa11536811297dfd472cef73
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.IR.code_forward, ZInQ.Compiler.IR.code_backward, ZInQ.Compiler.IR.lower_accepts_of_accepts, ZInQ.Compiler.IR.accepts_of_lower_halts, ZInQ.Compiler.IR.lower_halts_iff, ZInQ.Compiler.IR.lower_accepts_iff, ZInQ.Compiler.IR.lowering_correct
---

# Correctness of the lowering

Let $S$ be a program of the ideal register language with $k$ inputs, register bound
$\rho_S$ and lowering $\mathrm{low}(S)$ with $r$ registers.

0. (Open code) Say that a machine file $\sigma$ *simulates* a file $\rho$ if $\sigma(i)=\rho(i)$
   for $i<\rho_S$ and $\sigma(i)=0$ for $i\ge\rho_S$ (in particular the jump register and the
   auxiliary registers are zero). Let $S'$ be a statement of $S$ and let $\sigma$ simulate
   $\rho$. If $\langle S',\rho\rangle\Downarrow\mathrm{normal}(\rho')$, the run from the entry of
   $\mathrm{code}(S')$ with file $\sigma$ reaches its normal exit with a file simulating $\rho'$;
   if the outcome is $\mathrm{accept}$, it reaches the cleanup entry with every register
   $i\ge\rho_S$ zero; if it is $\mathrm{reject}$, it reaches the self-loop. Conversely, if the
   run from the entry with file $\sigma$ reaches a halt instruction after $t$ steps, then
   either $\langle S',\rho\rangle\Downarrow\mathrm{accept}$; or
   $\langle S',\rho\rangle\Downarrow\mathrm{normal}(\rho')$ and the run from the normal exit, with
   some file simulating $\rho'$, reaches a halt instruction within $t$ steps; or
   $\langle S',\rho\rangle\Downarrow\mathrm{reject}$ and the run from the self-loop reaches a halt
   instruction within $t$ steps.

For every $a\in\mathbb N^k$:

1. if $\langle S,\rho_0(a)\rangle\Downarrow\mathrm{accept}$, then $\mathrm{low}(S)$ accepts $a$ (it reaches
   its final halt with every register zero);
2. if $\mathrm{low}(S)$ halts on $a$ (reaches its final halt), then
   $\langle S,\rho_0(a)\rangle\Downarrow\mathrm{accept}$.

Hence $\mathrm{low}(S)$ halts on $a$ iff it accepts $a$ iff $S$ accepts $a$; for a total
program that rejects $a$, the run of $\mathrm{low}(S)$ never halts.

**Proof sketch.** *Blocks.* Each primitive block, entered with the jump register and its
auxiliary registers in the state required at block boundaries, reaches its exit after
finitely many steps with the register below $\rho_S$ updated to the exact value and every
other register restored (copies restore their source; snapshots make aliased operands safe;
saturating decrement is truncated subtraction; repeated addition is multiplication;
division maintains $y=r+qz+m$ with $0\le m<z$ while it moves the dividend unit by
unit). *Statements.* By induction on the derivation of $\langle S',\rho\rangle\Downarrow o$, the
run from the entry of the code of $S'$ with a file simulating $\rho$ reaches its normal exit
with a file simulating $\rho'$, the cleanup entry, or the self-loop, according to $o$; loops by induction on completed iterations.
Cleanup clears all registers and halts. (2) The run is deterministic and the final halt is
reachable only through cleanup, which is entered only from the code of $\mathbf{accept}$.
By induction on the statement and, for loops, strong induction on the length of the run
fragment from the entry, a fragment reaching a halt yields one of the three alternatives
of (0) for that statement (the fragment is a sequence of block executions mirroring the
semantics, so for a loop it contains finitely many iterations). At the top level the
second and third alternatives are impossible, since the run from the self-loop never
halts, so $\langle S,\rho_0(a)\rangle\Downarrow\mathrm{accept}$.

## Depends on

- [Lowering to primitive programs](lowering.md)
- [The ideal register language](structured-programs.md)
- [Register machines](register-machine.md)

## Sources

- [Section 10.3 lowering](../../../../sources/compiler-natural-locators.md#section-103-lowering)
