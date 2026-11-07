---
article_id: af_213974b61030ed333dcd79d6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Translation.precisionCircuit_wellFormed, ZInQ.Translation.powerTemplate_wellFormed
---

# Scope conditions of the natural precision circuit

Let $\mathcal N$ be the natural precision circuit (the circuit of the natural precision
polynomial $C$, obtained by specializing the universal halting circuit at the program
literal $c_3$) and $\mathcal P$ its power template. Then $\mathcal P$ is well-formed with bound $82$,
with explicit variables exactly $0,1,\dots,81$ in increasing order, $0,1,2$ the inputs, so that
its call blocks have $79$ variables; and $\mathcal N$ is well-formed with bound $1305811$, its $15845$
call nodes calling $\mathcal P$. In particular no variable node of the parent reads a private
coordinate of a power call.

**Proof sketch.** For $\mathcal P$: the power template has $3$ parameters and $79$ witnesses on
the variables $0,\dots,81$, and by its node statistics it has no call nodes and nontrivial
constants $4,2,3$, all at least $2$. For $\mathcal N$: by its shape it has $5$ inputs listed first
among $54056$ distinct explicit variables, $15845$ calls with blocks of $79$ variables, variable
count $1305811$, and nontrivial constants $c_3,2,4,1399$, where $c_3>1399\ge2$ by the size of the
program literal; by the specialization statement it is well scoped, so the blocks are pairwise
disjoint and disjoint from the explicit variables and every variable node refers to an
explicit variable. The remaining conditions (every operand of an addition, multiplication or
call node is an earlier node, and the root is a node) hold for the hash-consed node lists of
both constructions and are a closed decidable check, or follow from the construction.

## Depends on

- [Well-formed natural circuits](natural-circuit-well-formed.md)
- [Semantics of the natural precision polynomial](../natural/natural-polynomial-semantics.md)
- [The five-input natural precision circuit](../natural/universal/precision-circuit.md)

## Proof depends on

- [Size of the program literal](../natural/universal/wrapper-code-size.md)
- [The power template](../natural/formulas/power-template.md)
- [Node statistics of the halting circuit and the power template](../natural/universal/halting-node-check.md)
- [Shape of the natural precision circuit](../natural/universal/circuit-node-counts.md)
- [The precision circuit is a specialization](../natural/universal/precision-circuit-specialization.md)

## Sources

- [Section 10.4 parent](../../../sources/compiler-translation-locators.md#section-104-power-value-and-precision-parent)
- [Section 10.3 specialization](../../../sources/compiler-translation-locators.md#section-103-specialization)
- [Translation artifacts](../../../sources/compiler-translation-locators.md#translation-artifacts)
