---
article_id: af_ea81bd9a2a023d05a58dca6e
declaration: theorem
origin: cited
---

# Circuits of hierarchical constructions

Let a natural construction with $k$ inputs in hierarchical mode end with formula $\varphi$
and counter $V$, and let $\mathcal C$ be its natural circuit: its explicit variables are the
inputs and fresh variables in allocation order, its node list is the node encoding of
$\varphi$ with root the encoding of $\kappa(\varphi)$, and its call nodes are the power calls
with their blocks. Assume every macro argument is a polynomial in variables allocated
before the macro. Then:

1. $\mathcal C$ is well scoped, its variable count is $V$, and
   $[\![\mathcal C]\!]=\kappa(\varphi)$;
2. for every $c\in\mathbb N^k$, $Z_{\mathcal C}(c)$ holds if and only if there are natural values
   of the fresh variables for which $\varphi^\natural$ holds, where $\varphi^\natural$ is $\varphi$
   with every power call atom replaced by the relation $g_P=g_Q^{\,g_R}$ of its arguments;
3. consequently $Z_{\mathcal C}(c)$ is equivalent to the conjunction of the relations of
   the macros of the construction, as listed in the macro semantics, quantified over the
   remaining fresh variables.

The flat construction gives the same relation: replacing each power call by the flat
power macro changes the polynomial and the variable numbering but not the relation.

**Proof sketch.** (1) Induction over construction steps as in the specification
chapter's construction theorem: every node handed out denotes the polynomial of the
expression it was created for (hash-consing returns only structurally equal nodes), the
counter only grows, blocks are taken from it consecutively, and a block index is passed only
as a call's witness start, so no variable node refers to a block and the explicit variables
and blocks tile $[0,V)$. (2) By the compilation statement (items 1 and 3) together with the
power-template semantics, applied to the private blocks. (3) is (2) with the macro
semantics. The flat/hierarchical remark follows because both readings of a power call have
relation $P=Q^R$.

## Depends on

- [Natural constructions and their macros](natural-constructions.md)
- [Natural semantics of a natural circuit](natural-circuit-semantics.md)

## Proof depends on

- [Compilation and private witnesses over the naturals](natural-compilation.md)
- [Semantics of the power template](power-template-semantics.md)
- [Semantics of the natural macros](macro-semantics.md)

## Informally uses

- [Template construction from formulas](../../../syntax/language/builder-soundness.md)

## Sources

- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
- [Section 10.4 power blocks](../../../../sources/compiler-natural-locators.md#section-104-power-blocks)
