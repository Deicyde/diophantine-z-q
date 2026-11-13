---
article_id: af_80b23ccbd1db68dc81b335dd
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.isLContinuation_of_deuring, ZInQ.Contrib.HeckeFE.HeckeContinuation5, ZInQ.Contrib.HeckeFE.heckeContinuation5_of_deuring, ZInQ.Contrib.HeckeFE.heckeContinuation5_of_literature
---

# The continuation of $L(C_d,s)$ from Deuring's identity

*Hecke's continuation for $d\equiv5\pmod8$* is the following assertion: for every squarefree
natural number $d\equiv5\pmod8$, $L(C_d,s)$ has an [entire continuation](../l-series-continuation.md).
It is the case of [Hecke's continuation](../hecke-continuation.md) used by row 5b.

1. If $d$ is odd and squarefree and [Deuring's identity](deuring/deuring-identity.md) holds for $d$,
   then $L(C_d,s)$ has an entire continuation.
2. If Deuring's identity holds for every squarefree $d\equiv5\pmod8$, then Hecke's continuation for
   $d\equiv5\pmod8$ holds.
3. If, for every squarefree $d\equiv5\pmod8$, the Hecke coefficients have
   [the Euler product](gaussian/hecke-euler-product.md) for $d$ and
   [Gauss's theorem at the split primes](deuring/deuring-of-euler-product.md) holds for $d$, then
   Hecke's continuation for $d\equiv5\pmod8$ holds.

**Proof sketch.** (1) Let $c=\frac14\omega_d$, with $\omega_d$ the finite part of the
[Hecke character](gaussian/hecke-character.md) on $(\mathbb Z/4d)^2$.
[Hecke's continuation for periodic twists](theta/twisted-series.md) (3) gives an entire $G$ with
$G(s)=T_c(s)$ for $\operatorname{Re}s>3/2$. There
$L(C_d,s)=\sum_{n\ge1}c_d(n)n^{-s}$ ([the standard Euler product](../l-function-cd/l-series.md)
(1)), and by Deuring's identity and the Hecke character (1),
$c_d(n)=\lambda_d(n)=\sum_{\alpha\in A_n}c(\alpha\bmod4d)\,\alpha$ for $n\ge1$. Grouping by the norm
(periodic twists (4)) gives $L(C_d,s)=T_c(s)=G(s)$.

(2) $d\equiv5\pmod8$ is odd; apply (1).

(3) Deuring's identity holds for each such $d$
([from the Euler product](deuring/deuring-of-euler-product.md) (3)); apply (2).

## Depends on

- [Entire continuations of the L-series of an elliptic curve](../l-series-continuation.md)
- [Deuring's identity for $C_d$](deuring/deuring-identity.md)
- [The Euler product of $L(\psi_d,s)$](gaussian/hecke-euler-product.md)
- [Deuring's identity from the Euler product and the split primes](deuring/deuring-of-euler-product.md)

## Proof depends on

- [The Hecke character $\psi_d$](gaussian/hecke-character.md)
- [Periodic twists of the lattice series and their continuation](theta/twisted-series.md)
- [$L(C_d,s)$ is the Dirichlet series of the standard Euler product](../l-function-cd/l-series.md)

## Sources

- [Theta series and the method of Hecke](../../../../sources/hecke-locators.md#theta-series-and-the-method-of-hecke)
- [Hecke and Deuring](../../../../sources/rank-locators.md#hecke-and-deuring)
