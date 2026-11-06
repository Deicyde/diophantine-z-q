---
article_id: af_fa11536811297dfd472cef73
declaration: theorem
origin: cited
---

# Correctness of the lowering

Let $S$ be a program of the ideal register language with $k$ inputs, register bound
$\rho_S$ and lowering $\mathrm{low}(S)$ with $r$ registers.

0. (Open code) For every statement $S'$ of $S$ and file $\rho$ with the jump register and
   the auxiliary registers zero: if $\langle S',\rho\rangle\Downarrow\mathrm{normal}(\rho')$, the run
   from the entry of $\mathrm{code}(S')$ reaches its normal exit with file $\rho'$ (auxiliary
   and jump registers zero again); if the outcome is $\mathrm{accept}$ or $\mathrm{reject}$, it
   reaches the cleanup entry or the self-loop. Conversely a run from the entry that reaches
   the normal exit, the cleanup entry or the self-loop yields the corresponding derivation.

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
division maintains $y=qz+r$ and subtracts only when $r\ge z$). *Statements.* By induction on
the derivation of $\langle S',\rho\rangle\Downarrow o$, the run from the entry of the code of $S'$
with file $\rho$ (extended by zeros) reaches its normal exit with $\rho'$, the cleanup
entry, or the self-loop, according to $o$; loops by induction on completed iterations.
Cleanup clears all registers and halts. (2) The run is deterministic and the final halt is
reachable only through cleanup, which is entered only from the code of $\mathbf{accept}$;
by strong induction on the length of the run fragment from a statement's entry, a
fragment reaching cleanup yields a derivation of $\mathbf{accept}$ for that statement (the
fragment is a sequence of block executions mirroring the semantics, so for a loop it
contains finitely many iterations).

## Depends on

- [Lowering to primitive programs](lowering.md)
- [The ideal register language](structured-programs.md)
- [Register machines](register-machine.md)

## Sources

- [Section 10.3 lowering](../../../../sources/compiler-natural-locators.md#section-103-lowering)
