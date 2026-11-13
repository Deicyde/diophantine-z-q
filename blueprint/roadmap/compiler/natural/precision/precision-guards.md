---
article_id: af_f3a2eeb09bb6a83445db18b6
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Precision.admissible_of_ne_zero, ZInQ.Compiler.Precision.accepts_iff_tests
---

# Admissibility of nonzero indices

Assume $P_0$ has infinite order in $E(K_0)$. Then every $k\in\mathbb Z\setminus\{0\}$ is
admissible. Consequently, for $c\in\mathbb N^5$ passing the early tests of the precision
relation, the indices $l,a,j$ are admissible, and $\operatorname{accepts}(c)$ holds if and
only if the closeness and precision tests hold.

**Proof sketch.** For $k\ne0$, $[k]P_0\ne O$ since $P_0$ has infinite order. If its ordinate
were $0$ then $[k]P_0=-[k]P_0$, so $[2k]P_0=O$ with $2k\ne0$, again impossible. For inputs
passing the early tests, $l,a\ge1$ and $j=na\ne0$ because $n\ne0$ ($0\in\mathcal C$) and
$a\ne0$.

## Depends on

- [The precision relation](precision-relation.md)
- [The point $P_0$](../../../model/field/generator-point.md)

## Informally uses

- [The generator certificate](../../../model/generator.md)

## Sources

- [Section 10 decision predicate](../../../../sources/compiler-natural-locators.md#section-10-decision-predicate)
