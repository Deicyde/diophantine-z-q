---
article_id: af_213974b61030ed333dcd79d6
declaration: theorem
origin: cited
---

# Scope conditions of the natural precision circuit

Let $\mathcal N$ be the natural precision circuit (the circuit of the natural precision
polynomial $C$, obtained by specializing the universal halting circuit at the program
literal $c_3$) and $\mathcal P$ its power template. Then:

1. $\mathcal P$ has $3$ inputs, its explicit variables are exactly $0,1,\dots,81$ in increasing
   order with $0,1,2$ the inputs, it has no call nodes, every variable node refers to one of
   $0,\dots,81$, every operand of an addition or multiplication node is an earlier node, its
   root is a node, and its constants other than $0,1,-1$ are $4,2,3$. Hence $\mathcal P$ is
   well-formed with bound $82$, and its call blocks have $79$ variables.
2. $\mathcal N$ has $5$ inputs, its explicit variable indices are pairwise distinct with the
   inputs $0,\dots,4$ listed first, every variable node refers to an explicit variable, every
   operand of an addition, multiplication or call node is an earlier node, its root is a node,
   each of its $15845$ call nodes calls $\mathcal P$ with a block of $79$ variables, these blocks are
   pairwise disjoint and disjoint from the explicit variable indices, every explicit variable
   and every block variable is below $1305811$, and its constants other than $0,1,-1$ are
   $c_3,2,4,1399$ with $c_3\ge2$. Hence $\mathcal N$ is well-formed with bound $1305811$.

In particular no variable node of the parent reads a private coordinate of a power call.

Apart from $c_3\ge2$, each item is a closed decidable statement about the two explicit
circuits: scan the explicit variables, the nodes and the call blocks. The inequality
$c_3\ge2$ follows from the bound $c_3>1399$ on the program literal, without computing its
digits.

## Depends on

- [Well-formed natural circuits](natural-circuit-well-formed.md)
- [Semantics of the natural precision polynomial](../natural/natural-polynomial-semantics.md)
- [The five-input natural precision circuit](../natural/universal/precision-circuit.md)

## Proof depends on

- [Size of the program literal](../natural/universal/wrapper-code-size.md)

## Sources

- [Section 10.4 parent](../../../sources/compiler-translation-locators.md#section-104-power-value-and-precision-parent)
- [Section 10.3 specialization](../../../sources/compiler-translation-locators.md#section-103-specialization)
- [Translation artifacts](../../../sources/compiler-translation-locators.md#translation-artifacts)
