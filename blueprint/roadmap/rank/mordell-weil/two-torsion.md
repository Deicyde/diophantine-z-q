---
article_id: af_08a348003cc74e605918f7bc
declaration: theorem
origin: background
---

# The two-torsion of $C_n(\mathbb Q)$

> **The congruent-number route.** This page belongs to the congruent-number route to pole completeness, through Tian–Yuan–Zhang and Gross–Zagier. [Elliot's route](../../main/main-theorem.md) is the other route to the same theorem. This page's Lean declarations are not on this fork's main (fork issue #77); the route's Lean is kept at the tag `route-k-final` and pinned upstream in elliotglazer/diophantine-z-q.

Let $n$ be a positive integer and $C_n:y^2=x^3-n^2x$ over $\mathbb Q$. Then $C_n$ is an elliptic
curve, and for each $e\in\{0,n,-n\}$ the point $(e,0)$ is a nonsingular point of $C_n$. A point
$P\in C_n(\mathbb Q)$ satisfies $2P=O$ if and only if
$$P\in\{O,\ (0,0),\ (n,0),\ (-n,0)\}.$$
In particular exactly $4$ points $P\in C_n(\mathbb Q)$ satisfy $2P=O$.

**Proof sketch.** $C_n$ is the curve $E_b:y^2=x^3+bx$ with $b=-n^2\ne0$; its discriminant
$-64b^3=64n^6$ is nonzero, so $C_n$ is elliptic. Each $e\in\{0,\pm n\}$ is a root of
$x^3-n^2x=x(x-n)(x+n)$, so $(e,0)$ lies on $C_n$, and points of an elliptic curve are
nonsingular. Clearly $2O=O$. For an affine point $P=(x,y)$ we have $-P=(x,-y)$, so $2P=O$ if and
only if $y=0$; then $x(x-n)(x+n)=0$, that is $x\in\{0,n,-n\}$, and conversely. The four points
are distinct: $O$ is not affine, and $0,n,-n$ are distinct because $n\ne0$.

## Depends on

None.

## Sources

- [Two-torsion of the congruent number curves](../../../sources/rank-locators.md#two-torsion-of-the-congruent-number-curves)
