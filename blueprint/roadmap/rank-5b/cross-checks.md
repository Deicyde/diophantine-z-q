---
article_id: af_0266aad120a8752a17676e84
declaration: theorem
origin: bridged
---

# Two values of the row-5b determinant

> **The congruent-number route.** This page belongs to the congruent-number route to pole completeness, through Tian–Yuan–Zhang and Gross–Zagier. [Elliot's route](../main/main-theorem.md) is the other route to the same theorem. This page's Lean declarations are not on this fork's main (fork issue #77); the route's Lean is kept at the tag `route-k-final` and pinned upstream in elliotglazer/diophantine-z-q.

For $n=21=3\cdot7$, $\det M_{5b}=1$; for $n=5$, $\det M_{5b}=0$.

For $n=21$ this agrees with Corollary 4.4: by the note's computations, which are not part of
this statement, $C_{21}$ has a Selmer group with $8$ elements and $7$ is a first coordinate.

**Proof sketch.** The determinant is unchanged when the primes are relabelled. For $21$, with
the primes listed as $(3,7)$, the bits are $(7/3)_+=0$ and $(3/7)_+=1$, $y_3=y_7=1$, $z_3=1$,
$z_7=0$, and the $5\times5$ determinant over $\mathbb F_2$ is expanded along rows, a finite
computation. For $5$, $y_5=0$, so the bordering row of $M_{5b}$ vanishes.

## Depends on

- [Smith's matrices $L$, $M_1$ and $M_{5b}$](smith-matrices.md)

## Sources

- [Validation](../../sources/rank-5b-locators.md#validation)
