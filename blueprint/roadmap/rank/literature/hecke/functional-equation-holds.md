---
article_id: af_f2f311ced8f2038a4e9bb2fc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.functionalEquation5, ZInQ.Contrib.GaussFE.literature_hecke_fe
---

# The functional equation holds

1. [Hecke's continuation for $d\equiv5\pmod8$](continuation-of-deuring.md) and
   [the functional equation on the critical strip](../functional-equation.md) both hold.
2. The functional equation on the critical strip holds: for every squarefree natural number
   $d\equiv5\pmod8$, every entire continuation $F$ of $L(C_d,s)$ and every complex $s$ with
   $0<\operatorname{Re}s<2$, $\Lambda_{32d^2}(2-s)=-\Lambda_{32d^2}(s)$.

**Proof sketch.** (1) Gauss's point count [holds](gauss/gauss-point-count-holds.md), and
[Hecke's continuation for $d\equiv5\pmod8$ and the functional equation](both-from-gauss-count.md)
(2) applies. (2) is the second half of (1).

The proof follows Hecke: by Deuring's identity, which is proved from Gauss's point count, $L(C_d,s)$
is a periodic twist of the theta series of $\mathbb Z[i]$ modulo $4d$; the transformation law of the
theta kernels gives the functional equation of the completed twist, provided the finite Fourier
transform of the twist is supported on $(1+i)\mathbb Z[i]$, which is proved with quadratic Gauss
sums. The level $32d^2$ in the completed function (the classical conductor of $C_d$, which is not
computed here) and the sign $-1$ come out of that computation, the sign from
$\left(\frac2d\right)=-1$ for $d\equiv5\pmod8$.

So the functional equation, one of the five hypotheses of [the main theorem](../../../main/main-theorem.md),
is proved, with no hypothesis.

## Depends on

- [The functional equation of $L(C_d,s)$ on the strip $0<\operatorname{Re}s<2$](../functional-equation.md)
- [The continuation of $L(C_d,s)$ from Deuring's identity](continuation-of-deuring.md)

## Proof depends on

- [Gauss's point count holds](gauss/gauss-point-count-holds.md)
- [Hecke's continuation for $d\equiv5\pmod8$ and the functional equation from Gauss's point count](both-from-gauss-count.md)

## Sources

- [The Hecke section](../../../../sources/hecke-locators.md#the-hecke-section)
- [The functional equation and the root number](../../../../sources/rank-locators.md#the-functional-equation-and-the-root-number)
