---
article_id: af_1c24093bb3d036f795f93a6a
declaration: theorem
origin: cited
---

# One interpreter loop simulates one instruction

Call a configuration of $\mathcal U$ *coherent* with a virtual configuration $(i,\rho)$ of
$\mu_e$ when it is at the entry of the main loop, registers hold $w\ge1$, $D$ and $\beta=2^w$
of $e$, the virtual state register holds $\mathrm{pc}=i$, the tape register holds a list
code representing $\rho$, and the jump register and all scratch registers are zero. From a
coherent configuration:

1. if $\mu_e(i)=\mathrm{halt}$, the run of $\mathcal U$ reaches the cleanup entry after finitely
   many steps;
2. otherwise it returns, after finitely many steps and without passing through cleanup, to
   a configuration coherent with the successor of $(i,\rho)$ under $\mu_e$.

**Proof sketch.** Compose the block contracts: digit extraction by repeated division yields
exactly $d_{4i},\dots,d_{4i+3}$ (missing digits are zero); the opcode test admits exactly $1$
and $2$; getList and setList realize the read and the update of entry $j$; copies restore
their sources and the jump register stays zero, so the invariant registers are preserved.
Every block terminates, so one loop iteration executes exactly one decoded instruction
with finite work.

## Depends on

- [The universal interpreter](universal-interpreter.md)
- [The universal program numbering](program-numbering.md)

## Proof depends on

- [Arithmetic blocks of the interpreter](interpreter-primitives.md)
- [List blocks of the interpreter](interpreter-list-primitives.md)
- [Tape lists](tape-lists.md)

## Sources

- [Section 10.3 interpreter](../../../../sources/compiler-natural-locators.md#section-103-interpreter)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
