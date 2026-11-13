---
article_id: af_ac32eba3c4e55b2d64468602
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.heckeContinuation, ZInQ.Contrib.heckeContinuation_of_gaussPointCount, ZInQ.Contrib.heckeContinuation_functionalEquation5_of_gaussPointCount
---

# Hecke's continuation holds

1. [Gauss's point count](gauss/gauss-point-count.md) implies
   [Hecke's continuation](../hecke-continuation.md): for every natural number $d\ne0$, $L(C_d,s)$
   has an entire continuation.
2. Gauss's point count implies Hecke's continuation and
   [the functional equation on the critical strip](../functional-equation.md).
3. Hecke's continuation holds.

**Proof sketch.** (1) Let $d\ne0$ and write $d=m^2a$ with $a$ squarefree; $m\ne0$ and $a\ne0$. By
[the continuation for every squarefree $d$](every-d/continuation-squarefree.md) (2), $L(C_a,s)$ has
an entire continuation $F$. By [the square factor](every-d/cd-square-factor.md) (3),
$L(C_{m^2a},s)=L(C_a,s)$ for every $s$, so $F$ is also an entire continuation of $L(C_d,s)$.

(2) Hecke's continuation by (1), and the functional equation by
[Hecke's continuation for $d\equiv5\pmod8$ and the functional equation](both-from-gauss-count.md) (2).

(3) Gauss's point count [holds](gauss/gauss-point-count-holds.md); apply (1).

So Hecke's continuation, one of the five hypotheses of [the main theorem](../../../main/main-theorem.md),
is proved, with no hypothesis.

## Depends on

- [Hecke's continuation of $L(C_d,s)$](../hecke-continuation.md)
- [The functional equation of $L(C_d,s)$ on the strip $0<\operatorname{Re}s<2$](../functional-equation.md)
- [Gauss's point count on $y^2=x^3-x$](gauss/gauss-point-count.md)

## Proof depends on

- [The continuation of $L(C_d,s)$ for every squarefree $d$, from Gauss's point count](every-d/continuation-squarefree.md)
- [$L(C_{m^2d},s)=L(C_d,s)$](every-d/cd-square-factor.md)
- [Hecke's continuation for $d\equiv5\pmod8$ and the functional equation from Gauss's point count](both-from-gauss-count.md)
- [Gauss's point count holds](gauss/gauss-point-count-holds.md)

## Sources

- [The Hecke section](../../../../sources/hecke-locators.md#the-hecke-section)
- [Hecke and Deuring](../../../../sources/rank-locators.md#hecke-and-deuring)
