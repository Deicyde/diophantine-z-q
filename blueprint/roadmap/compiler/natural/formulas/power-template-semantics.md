---
article_id: af_473fbb0e3cc36b56aea8f251
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Natural.powerTemplate_natRel, ZInQ.Compiler.Natural.powerSpec_hierarchical_powerTemplate
---

# Semantics of the power template

For all natural numbers $P,Q,R$:
$$\bigl(\exists w\in\mathbb N^{79},\ \mathcal P(P,Q,R,w)=0\bigr)\iff P=Q^R,$$
with $0^0=1$. Consequently, in any natural construction in hierarchical mode, a power call
whose argument polynomials take natural values at every natural point and whose block is
private (pairwise disjoint from the other blocks and occurring in no other atom or argument)
may be replaced by the relation $g_P=g_Q^{\,g_R}$ of its argument values.

**Proof sketch.** By the compilation statement, $\mathcal P(P,Q,R,w)=0$ iff the flat power
formula holds naturally at $(P,Q,R,w)$; by item 2 of that statement the existential over
the $79$ witnesses distributes over the three branches and over the conjuncts of each
branch, the witnesses of the two inactive branches being set to $0$. The branch conditions
are those of the power formula once the gadgets and the three alpha macros are replaced by
their relations (equational gadgets, alpha soundness and completeness). The power formula
expresses exponentiation.

## Depends on

- [The power template](power-template.md)

## Proof depends on

- [Compilation and private witnesses over the naturals](natural-compilation.md)
- [The equational gadgets over the naturals](natural-atom-gadgets.md)
- [Soundness of the alpha formula](../exponential/alpha-equations-sound.md)
- [Completeness of the alpha formula](../exponential/alpha-equations-complete.md)
- [The power formula expresses exponentiation](../exponential/power-equations-correct.md)

## Sources

- [Section 10.2 power formula](../../../../sources/compiler-natural-locators.md#section-102-power-formula)
- [Section 10.4 power blocks](../../../../sources/compiler-natural-locators.md#section-104-power-blocks)
