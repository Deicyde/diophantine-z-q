---
article_id: af_e888918459f9445b7ee53d90
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.Compiler.Natural.NatCircuit, ZInQ.Compiler.Natural.NatCircuit.poly, ZInQ.Compiler.Natural.NatCircuit.NatRel, ZInQ.Compiler.Natural.NatCircuit.WellScoped
---

# Natural semantics of a natural circuit

Let $\mathcal C$ be a natural circuit in the format of the specification chapter: $k$
inputs, a list of explicit variables (inputs first, with indices $0,\dots,k-1$), a node list
of constants, variables, additions, multiplications and calls $\mathrm{call}\,(a,b,c)\,w$ of
the power template on three earlier nodes with block start $w$, a root node, and a variable
count $V$ (the number of explicit variables plus $79$ times the number of calls, when the
blocks and explicit variables tile $[0,V)$).

1. The *polynomial* $[\![\mathcal C]\!]\in\mathbb Z[X_i:i\in\mathbb N]$ is the denotation of
   the root under the template semantics of the specification chapter, a call node
   denoting the power call $\mathcal P\bigl[[\![a]\!],[\![b]\!],[\![c]\!];w\bigr]$ (literal
   substitution).
2. The *natural relation* of $\mathcal C$ is the predicate on $\mathbb N^k$
   $$Z_{\mathcal C}(c_0,\dots,c_{k-1})\iff\exists z\in\mathbb N^{V-k},\ \
   [\![\mathcal C]\!](c_0,\dots,c_{k-1},z)=0 ,$$
   the variables of index at least $V$, if any occur, being set to $0$.
3. $\mathcal C$ is *well scoped* if every block $[w,w+79)$ lies in $[k,V)$, the blocks are
   pairwise disjoint and disjoint from the explicit variables, the explicit variables and
   blocks together cover $[0,V)$, and every variable node refers to an explicit variable.

This is a definition. Item 2 quantifies over natural witnesses only; replacing
$\mathbb N$ by $\mathbb Q$ here is not justified, and the translation to rational point codes is
the subject of the next section.

## Depends on

- [Translation of a natural circuit into a model-evaluation recipe](../../../syntax/recipes/model-evaluation-translation.md)
- [Semantics of templates and recipes](../../../syntax/template-semantics.md)
- [The power template](power-template.md)

## Sources

- [Section 10.4 power blocks](../../../../sources/compiler-natural-locators.md#section-104-power-blocks)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
