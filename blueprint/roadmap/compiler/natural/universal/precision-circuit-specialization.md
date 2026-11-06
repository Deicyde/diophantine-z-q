---
article_id: af_87d292690d64885d4a6b6e34
declaration: theorem
origin: cited
---

# The precision circuit is a specialization

Let $\theta$ be the substitution $X_0\mapsto c_3$, $X_1\mapsto X_5$, $X_i\mapsto X_{i+7}$ for $i\ge2$.
Then
$$[\![\mathcal N]\!]=\theta\bigl([\![\mathcal H]\!]\bigr)^2+\sum_{i=0}^3\Bigl(2X_{5+i}-(X_i+t_{i+1})(X_i+t_{i+1}+1)-2t_{i+1}\Bigr)^2,$$
with $t_{i+1}=X_{6+i}$ for $i<3$ and $t_4=X_4$. Consequently, for every $c\in\mathbb N^5$,
$$Z_{\mathcal N}(c)\iff Z_{\mathcal H}(c_3,\operatorname{enc}_5(c)).$$
The pairing variables $X_5,\dots,X_8$ are disjoint from the inputs and from the shifted
variables of $\mathcal H$, and the shifted blocks remain private.

**Proof sketch.** Node by node, the denotation of each modified node of $\mathcal H$ is $\theta$
applied to the original denotation: variable nodes by definition, constants unchanged,
additions and multiplications by the homomorphism property, and calls because shifting
the block start by $7$ commutes with $\theta$ on the callee's witness variables. The appended
nodes denote the four pairing polynomials and the sum of squares. For the relation: a
natural zero makes every square vanish (integers), so the pairing equations hold and, by
unique Cantor unpairing, $t_0=\operatorname{enc}_5(c)$; then $\theta([\![\mathcal H]\!])=0$ is a natural
zero of $\mathcal H$ at $(c_3,\operatorname{enc}_5(c))$ after renaming. Conversely take $t_i$ the
Cantor values and the witnesses of $\mathcal H$ shifted by $7$.

## Depends on

- [The five-input natural precision circuit](precision-circuit.md)
- [Cantor pairing and its decoder](../programs/cantor-pairing.md)

## Proof depends on

- [Unique Cantor unpairing](../programs/cantor-unpairing.md)
- [Compilation and private witnesses over the naturals](../formulas/natural-compilation.md)

## Sources

- [Section 10.1 wrapper specialization](../../../../sources/compiler-natural-locators.md#section-101-wrapper-specialization)
- [Section 10.3 specialization](../../../../sources/compiler-natural-locators.md#section-103-specialization)
