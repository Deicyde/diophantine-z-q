---
article_id: af_106a3a57d021fd5dd896df13
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.NodeCheck.HaltingAddMulBound, ZInQ.Compiler.NodeCheck.haltingAddMulBound, ZInQ.Compiler.NodeCheck.haltingCircuit_varNodes, ZInQ.Compiler.NodeCheck.haltingCircuit_constNodes, ZInQ.Compiler.NodeCheck.haltingCircuit_constList, ZInQ.Compiler.Universal.haltingCircuit_countKind_call, ZInQ.Compiler.Universal.haltingCircuit_nodes_eq, ZInQ.Compiler.Universal.powerTemplate_nodeStats, ZInQ.Compiler.Universal.powerTemplate_nodes_length
---

# Node statistics of the halting circuit and the power template

1. The node list of the universal halting circuit $\mathcal H$ has at most $125{,}307$
   additions and at most $98{,}361$ multiplications, $54{,}049$ variable nodes, $6$ constant
   nodes with values $0,1,2,4,1399,-1$ in node order, and $15{,}845$ calls. Its first two nodes
   are the variable nodes of $X_0$ and $X_1$.
2. The node list of the power template $\mathcal P$ has $474$ nodes: $82$ variable nodes, $6$
   constant nodes with values $0,1,4,2,3,-1$ in node order, $196$ additions,
   $190$ multiplications and no calls.

Neither item involves $c_3$ or any astronomically large constant.

**Proof sketch.** Item 2 is a closed computation on the $474$ nodes of the flat power macro.
Item 1 is proved without evaluating the construction. The variable nodes are the explicit
variables; the constants are $0,1,2$ (the only ones the gadgets and macros request), $4$ and
the program size $1399$ (requested by the first item of the packed construction) and $-1$
(requested by the encoding), first occurring in this order; the calls are counted by the
compiler. For the two bounds, count the addition and
multiplication nodes the construction requests, $129{,}408$ and $98{,}727$, and subtract the
requests whose node is already present: the re-sum $z+a$ inside every bit conjunction
($2{,}452$ additions), the re-sum $N+1$ in every mask binomial after the first ($1{,}601$
additions), the product $K\cdot F$ in every register mask after the first ($204$
multiplications), repeats in the state equations of the halting step ($48$ additions and
$151$ multiplications) and $11$ repeated products of the encoding. That a node is present
depends only on how it was requested earlier, so no statement about the other nodes is needed.

## Depends on

- [The universal halting circuit](halting-polynomial.md)
- [The power template](../formulas/power-template.md)

## Sources

- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
