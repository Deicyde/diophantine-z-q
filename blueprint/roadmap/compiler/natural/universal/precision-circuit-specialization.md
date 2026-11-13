---
article_id: af_87d292690d64885d4a6b6e34
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Universal.precisionCircuit_poly, ZInQ.Compiler.Universal.precisionCircuit_natRel_iff, ZInQ.Compiler.Universal.precisionCircuit_wellScoped
---

# The precision circuit is a specialization

Let $\theta$ be the substitution $X_0\mapsto c_3$, $X_1\mapsto X_5$, $X_i\mapsto X_{i+7}$ for $i\ge2$.
Then
$$[\![\mathcal N]\!]=\theta\bigl([\![\mathcal H]\!]\bigr)^2+\sum_{i=0}^3\Bigl(2X_{5+i}-(X_i+t_{i+1})(X_i+t_{i+1}+1)-2t_{i+1}\Bigr)^2,$$
with $t_{i+1}=X_{6+i}$ for $i<3$ and $t_4=X_4$. Consequently, for every $c\in\mathbb N^5$,
$$Z_{\mathcal N}(c)\iff Z_{\mathcal H}(c_3,\operatorname{enc}_5(c)).$$
Moreover $\mathcal N$ is well scoped: the pairing variables $X_5,\dots,X_8$ are disjoint from
the inputs and from the shifted variables and blocks of $\mathcal H$, the shifted blocks are
pairwise disjoint and disjoint from the explicit variables, and no variable node of
$\mathcal N$ refers to a block variable. In particular no parent variable node accesses a
private coordinate of a power call.

**Proof sketch.** Node by node, the denotation of each modified node of $\mathcal H$ is $\theta$
applied to the original denotation: variable nodes by definition, constants unchanged,
additions and multiplications by the homomorphism property, and calls because shifting
the block start by $7$ commutes with $\theta$ on the callee's witness variables. The appended
nodes denote the four pairing polynomials and the sum of squares. For the relation: a
natural zero makes every square vanish (integers), so the pairing equations hold and, by
unique Cantor unpairing, $t_0=\operatorname{enc}_5(c)$; then $\theta([\![\mathcal H]\!])=0$ is a natural
zero of $\mathcal H$ at $(c_3,\operatorname{enc}_5(c))$ after renaming. Conversely take $t_i$ the
Cantor values and the witnesses of $\mathcal H$ shifted by $7$. Well-scopedness: $\mathcal H$ is
well scoped (its counting statement), its variables and blocks lie in $[2,1{,}305{,}804)$, so after
the shift they lie in $[9,1{,}305{,}811)$, disjoint from the new explicit variables
$0,\dots,8$; the shift is injective, so disjointness and the absence of variable nodes inside
blocks are preserved, and the appended nodes refer only to $X_0,\dots,X_8$.

## Depends on

- [The five-input natural precision circuit](precision-circuit.md)
- [Cantor pairing and its decoder](../programs/cantor-pairing.md)
- [Natural semantics of a natural circuit](../formulas/natural-circuit-semantics.md)

## Proof depends on

- [Unique Cantor unpairing](../programs/cantor-unpairing.md)
- [Compilation and private witnesses over the naturals](../formulas/natural-compilation.md)
- [Counts of the universal halting circuit](halting-circuit-counts.md)

## Sources

- [Section 10.1 wrapper specialization](../../../../sources/compiler-natural-locators.md#section-101-wrapper-specialization)
- [Section 10.3 specialization](../../../../sources/compiler-natural-locators.md#section-103-specialization)
