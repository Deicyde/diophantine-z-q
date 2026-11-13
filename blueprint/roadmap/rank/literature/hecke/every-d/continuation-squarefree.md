---
article_id: af_2eb53120e758e95195659432
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeAll.twChar, ZInQ.Contrib.HeckeAll.twChar_intCast, ZInQ.Contrib.HeckeAll.isLContinuation_of_squarefree
---

# The continuation of $L(C_d,s)$ for every squarefree $d$, from Gauss's point count

For a natural number $d$ define on $(\mathbb Z/4d)^2$
$$t_d(x)=\frac14\left(\frac d{\tilde x_1^2+\tilde x_2^2}\right)u(\tilde x_1\bmod4,\ \tilde x_2\bmod4),$$
where $\tilde x_1,\tilde x_2\in\{0,\dots,4d-1\}$ are the least residues of the coordinates of $x$,
$u$ is the [primary unit](../gaussian/primary-unit.md), and $\left(\frac dn\right)$ is the Jacobi
symbol as in [the Hecke character](../gaussian/hecke-character.md), here with $d$ as the numerator.

1. Let $d\ne0$, $n$ a natural number and $\alpha\in A_n$ (a
   [Gaussian integer of norm $n$](../gaussian/norm-fibres.md)). Then
   $t_d(\alpha\bmod4d)=\frac14\left(\frac dn\right)u(\alpha)$.
2. If [Gauss's point count](../gauss/gauss-point-count.md) holds and $d$ is squarefree, then
   $L(C_d,s)$ has an [entire continuation](../../l-series-continuation.md).

**Proof sketch.** (1) $u(\tilde\alpha)=u(\alpha)$ as $\tilde\alpha\equiv\alpha\pmod4$. If
$u(\alpha)=0$ both sides vanish. Otherwise $n$ is odd: if $n$ were even, then
$2(\alpha_1^2+\alpha_2^2)\equiv0\pmod4$ and $u(\alpha)=0$
([primary unit](../gaussian/primary-unit.md) (4)). Then $\tilde n=\tilde\alpha_1^2+\tilde\alpha_2^2$
is odd and congruent to $n$ modulo $4d$, and for odd denominators the symbol
$\left(\frac d\cdot\right)$ depends only on the denominator modulo $4d$, so
$\left(\frac d{\tilde n}\right)=\left(\frac dn\right)$.

(2) Deuring's identity holds for $d=1$
([from Gauss's point count](../deuring/deuring-from-gauss-count.md)), so
$c_1(n)=\frac14\sum_{\alpha\in A_n}u(\alpha)\alpha$ for $n\ge1$. By
[the quadratic twist](quadratic-twist-coefficients.md) (5) and (1), for $n\ge1$
$$c_d(n)=\left(\frac dn\right)c_1(n)=\sum_{\alpha\in A_n}t_d(\alpha\bmod4d)\,\alpha.$$
[Hecke's continuation for periodic twists](../theta/twisted-series.md) (3) gives an entire $G$ with
$G(s)=T_{t_d}(s)$ for $\operatorname{Re}s>3/2$. There,
$L(C_d,s)=\sum_{n\ge1}c_d(n)n^{-s}$ ([$L(C_d,s)$ for every squarefree $d$](cd-coefficients-every-squarefree.md)
(5)), and grouping by the norm (periodic twists (4)) identifies this with $T_{t_d}(s)=G(s)$.

## Depends on

- [The primary unit of a Gaussian integer modulo 4](../gaussian/primary-unit.md)
- [Gaussian integers as pairs, norms and units](../gaussian/norm-fibres.md)
- [Gauss's point count on $y^2=x^3-x$](../gauss/gauss-point-count.md)
- [Entire continuations of the L-series of an elliptic curve](../../l-series-continuation.md)

## Proof depends on

- [Deuring's identity for $d\equiv1\pmod4$ from Gauss's point count](../deuring/deuring-from-gauss-count.md)
- [The coefficients of $C_d$ as a quadratic twist of $C_1$](quadratic-twist-coefficients.md)
- [Periodic twists of the lattice series and their continuation](../theta/twisted-series.md)
- [$L(C_d,s)$ for every squarefree $d$](cd-coefficients-every-squarefree.md)

## Sources

- [The curves for even and non-squarefree d](../../../../../sources/hecke-locators.md#the-curves-for-even-and-non-squarefree-d)
- [Theta series and the method of Hecke](../../../../../sources/hecke-locators.md#theta-series-and-the-method-of-hecke)
