---
article_id: af_91b0b02411929769390cfde9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Symbols.two_symbol_address
---

# Lemma 7.12: two symbols on one address family

Assume that $A_1$ and $A_2$ satisfy [the coefficient rules](lemma-7-6-coefficient-rules.md). Let
$b\ge1$ and let $\Gamma$ be a compatible typed graph in which every vertex has a nonzero activation
$\lambda_v\in\mathbb F_2^b$ and every nonzero activation is carried by some vertex. Suppose that at every
address $x\ne0$ the active configuration $\Gamma_x$ has nonzero terminal polynomial for $A_1$ and for
$A_2$. Then there is a compatible $\Gamma'\supseteq\Gamma$ such that:

- the vertices of $\Gamma$, their types, mutual bits and activations are unchanged;
- every new vertex has type $0$ and a nonzero activation;
- $A_1(\Gamma'_x)=A_2(\Gamma'_x)=1$ at every $x\ne0$.

The zero address is unchanged, since no new vertex is present there.

The two symbols read the same alphabet in Lean; symbols reading projections of a common alphabet, as
in the manuscript, are composed with the projections, which preserves the rules
(`coefficientRules_comp`). One symbol is the case $A_1=A_2$. The manuscript's hypotheses that each
$\Gamma_x$ is nonempty and in every filter are implied, and its clause on prime representatives is not
part of the statement.

**Proof sketch.** As in the manuscript, by the network construction of Appendix G. The anchors give
the row-sum identity on every active restriction. A degree count on the product of the two top forms,
in the ordinary polynomial ring before Boolean reduction, has a nonzero coefficient; it selects one
singular or varying program per variable, and installing the corresponding networks gives a single
assignment that works for both symbols at every nonzero address. The symbols need no common nonzero
value beforehand.

## Depends on

- [Section 7: addresses and terminal polynomials](README.md)
- [Lemma 7.6: the coefficient rules](lemma-7-6-coefficient-rules.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
