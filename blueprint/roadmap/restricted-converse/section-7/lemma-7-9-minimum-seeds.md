---
article_id: af_34ed177435c29bed1eb37a06
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Symbols.minSeed_bits_irrelevant, ZInQ.Manuscript.RC.Symbols.partitionable_terminalNonzero, ZInQ.Manuscript.RC.Symbols.partitionable_of_anchors
---

# Lemma 7.9: minimum seeds and contraction certificates

Assume that $A$ satisfies [the coefficient rules](lemma-7-6-coefficient-rules.md).

1. If $\Gamma$ is a minimum nonempty seed of $A$, then $A(\Delta)=1$ for every compatible $\Delta$ with
   the same vertices and the same types as $\Gamma$: the value does not depend on the internal pair
   bits.
2. If a compatible $\Gamma$ is partitionable, its terminal polynomial is nonzero: some change of its
   pair bits makes $A$ equal to one.
3. Let $\Gamma_0$ be a minimum nonempty seed with $r$ vertices and $s$ one of them. If a compatible
   $\Gamma$ has the same total type as $\Gamma_0$, contains distinct anchors of the types of the $r-1$
   vertices of $\Gamma_0$ other than $s$, and has at least one vertex besides the anchors, then $\Gamma$
   is partitionable.

In Lean a contraction certificate is a forest on the vertices of $\Gamma$ whose contraction has symbol
one; its trees are the contraction trees of the clusters. The reduction of Theorem 5.3 uses
`partitionable_of_anchors`, which applies `minSeed_bits_irrelevant`, through `auxFactor_of_inputs`; in
the remaining branch it uses all three parts through `final_family_graphs`.

**Proof sketch.** If $r\ge2$, a nonzero derivative in an internal bit would, by the contraction rule,
give a unit seed on $r-1$ nonempty vertices, contradicting minimality; if $r=1$ there is no internal
bit. Iterating the contraction rule along a forest gives the contracted symbol, so a certificate with
output one makes the iterated difference, and hence the polynomial, nonzero. For the third part keep
the anchors as singleton clusters and merge the remainder into one cluster; equal total types force
its type to be that of $s$, and by the first part the internal bits do not matter.

## Depends on

- [Section 7: unit seeds and partitionable lists](README.md)
- [Lemma 7.6: the coefficient rules](lemma-7-6-coefficient-rules.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
