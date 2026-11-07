---
article_id: af_609f251e689e14dc1f06d275
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.RM.Instr, ZInQ.Compiler.RM.Machine, ZInQ.Compiler.RM.Config, ZInQ.Compiler.RM.step, ZInQ.Compiler.RM.Halts, ZInQ.Compiler.RM.Program, ZInQ.Compiler.RM.Program.Valid, ZInQ.Compiler.RM.Program.Accepts
---

# Register machines

**Instructions.** An instruction is $\mathrm{inc}(j,x)$ (increment register $j$, go to state
$x$), $\mathrm{dec}(j,x,y)$ (if register $j$ is positive, decrement it and go to $x$;
otherwise go to $y$) or $\mathrm{halt}$. Registers are indexed by $\mathbb N$ and hold natural
numbers; a register file is a map $\rho:\mathbb N\to\mathbb N$.

**Machines and virtual halting.** A *machine* is a map $\mu:\mathbb N\to$ instructions. A
configuration is a pair $(i,\rho)$ of a state and a register file; the step relation
executes $\mu(i)$ and is undefined at a halt instruction. The run of $\mu$ from $(0,\rho_0)$
*halts* if it reaches, after finitely many steps, a state $i$ with $\mu(i)=\mathrm{halt}$.

**Primitive programs.** A *primitive program* is a list $p=(p_0,\dots,p_{m-1})$, $m\ge1$, of
instructions. It is *valid for $r$ registers* if $p_{m-1}=\mathrm{halt}$, no other
instruction is a halt, every register index is below $r$ and every target is below $m$.
It induces the machine with $\mu(i)=p_i$ for $i<m$ and $\mu(i)=\mathrm{halt}$ for $i\ge m$.
For $k\le r$ and inputs $a\in\mathbb N^k$ the *initial file* has $\rho_0(i)=a_i$ for $i<k$ and
$0$ otherwise. A valid $p$

- *halts on* $a$ if its run from $(0,\rho_0)$ reaches the final state $m-1$;
- *accepts* $a$ if its run reaches the final state $m-1$ with every register zero.

The number of *add instructions* (increments), *sub instructions* (decrements) and
registers $r$ are the *shape* of $p$. Since a valid program halts only at its final state,
a run reaches it at most once and then stops.

This is a definition. Acceptance is the convention of the packed compiler; halting is the
convention of the universal numbering; a cleanup stage that clears every register before
the final halt converts the second into the first.

## Depends on

None.

## Sources

- [Section 10.1 packed histories](../../../../sources/compiler-natural-locators.md#section-101-packed-histories)
- [Section 10.3 numbering](../../../../sources/compiler-natural-locators.md#section-103-numbering)
- [Compiler specification](../../../../sources/compiler-natural-locators.md#compiler-specification)
- [Compiler source](../../../../sources/compiler-natural-locators.md#compiler-source)
