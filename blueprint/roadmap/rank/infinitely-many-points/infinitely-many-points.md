---
article_id: af_3058f0d2dcbf49d900d5ce1b
declaration: def
origin: bridged
---

# Infinitely many rational solutions of $y^2=x^3-d^2x$

> **The congruent-number route.** This page belongs to the congruent-number route to pole completeness, through Tian–Yuan–Zhang and Gross–Zagier. [Elliot's route](../../main/main-theorem.md) is the other route to the same theorem. This page's Lean declarations are not on this fork's main (fork issue #77); the route's Lean is kept at the tag `route-k-final` and pinned upstream in elliotglazer/diophantine-z-q.

For a natural number $d$, the curve $y^2=x^3-d^2x$ has infinitely many rational points when the set
$$\{(x,y)\in\mathbb Q^2 : y^2=x^3-d^2x\}$$
of its affine rational solutions is infinite.

The statement involves only rational solutions of one equation: no group law, no point at infinity
and no condition on $d$.

**Remark (classical meaning).** For a squarefree positive integer $d$, the curve $y^2=x^3-d^2x$
having infinitely many rational points is the classical statement that $d$ is a congruent number.
This is a remark about what the condition means classically; it is not proved here, and no article
uses it.

## Depends on

None.

## Sources

- [The infinitely-many-points forms](../../../sources/rank-locators.md#the-infinitely-many-points-forms)
