---
article_id: af_97ea9ad0fa6dfaedf979fb9c
declaration: theorem
origin: bridged
---

# Two values of the genus sum

> **The congruent-number route.** This page belongs to the congruent-number route to pole completeness, through Tian–Yuan–Zhang and Gross–Zagier. [Elliot's route](../../main/main-theorem.md) is the other route to the same theorem. This page's Lean declarations are not on this fork's main (fork issue #77); the route's Lean is kept at the tag `route-k-final` and pinned upstream in elliotglazer/diophantine-z-q.

$T_{5b}(21)=1$ and $T_{5b}(5)=0$.

**Proof sketch.** Both $21=3\cdot7$ and $5$ are squarefree and $\equiv5\pmod8$, so by Theorem 3.6
the values are those of $\det M_{5b}$, which is $1$ for $n=21$ and $0$ for $n=5$. For $n=5$ there is
also a direct argument: the only set partition of $\{5\}$ has the single block $\{5\}$, with
$d_B=5$, so no partition has a block with $d_B\equiv7\pmod8$ and the sum is empty.

## Depends on

- [The genus sum $T_{5b}$](genus-sum.md)

## Proof depends on

- [Row 5b of Smith's table (Theorem 3.6)](theorem-3-6.md)
- [Two values of the row-5b determinant](../cross-checks.md)

## Sources

- [Theorem 3.6](../../../sources/rank-5b-locators.md#theorem-36)
- [Validation](../../../sources/rank-5b-locators.md#validation)
