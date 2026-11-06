---
article_id: af_e7cad9833f61fcbb5996e607
declaration: theorem
origin: cited
---

# The lowered machine halts exactly on acceptance

For every structured register program $S$ and every input $\mathbf x\in\mathbb N^t$ with $t\le N_S$:

1. if $S$ accepts $\mathbf x$, then $\operatorname{lower}(S)$ accepts $\mathbf x$: its run reaches the final
   halt with all registers zero;
2. if $\operatorname{lower}(S)$ halts on $\mathbf x$, then $S$ accepts $\mathbf x$.

Hence $\operatorname{lower}(S)$ halts on $\mathbf x$ iff it accepts $\mathbf x$ iff $S$ accepts $\mathbf x$; in
particular rejection and divergence of $S$ both give a run that never halts, even when $S$ is
total.

**Proof sketch.** *Block lemma.* For every statement $S'$ of $S$ and registers $R$ whose
auxiliary registers are zero: if $S',R\Downarrow\mathrm{cont}(R')$, the block of $S'$ runs from its
entry state with $R$ to its exit state with registers agreeing with $R'$ below $N_S$ and zero
auxiliaries, in finitely many steps; $\mathrm{acc}$ reaches the cleanup block and $\mathrm{rej}$ the
self-loop. It is proved by induction on the derivation. The primitive cases are finite loops
whose counters (the emptied register, the copy of $r''$, the remainder) strictly decrease;
copies restore their source, snapshots make aliasing harmless, the reserved register stays
zero, and the division maintains $x=q\,y+\text{rem}$ with $\text{rem}<y$ at exit. Loops follow by
induction on the number of completed iterations. *Converse.* If the run of the block of $S'$
from $R$ reaches a halting configuration or leaves the block, then $S',R$ has an outcome
and the exit taken is the one of that outcome; induct on the number of machine steps, using
that each primitive block is a terminating loop and that the rejection self-loop and the
loop back to a $\mathbf{while}$ test are the only backward jumps. The cleanup block halts with all
registers zero; the self-loop never halts.

## Depends on

- [Lowering to a primitive program](lowering.md)
- [Structured register programs](structured-programs.md)

## Sources

- [Section 10.3 lowering](../../../../sources/compiler-translation-locators.md#section-103-lowering)
- [Section 10.3 interpreter](../../../../sources/compiler-translation-locators.md#section-103-interpreter)
