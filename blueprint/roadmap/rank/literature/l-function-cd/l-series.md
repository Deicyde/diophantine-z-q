---
article_id: af_a0ff1efde53216e94fc47a23
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Literature.cdCoeff, ZInQ.Literature.LSeries_cd_eq, ZInQ.Literature.LSeries_cd_eq_of_mod_eight
---

# $L(C_d,s)$ is the Dirichlet series of the standard Euler product

For natural numbers $d$ and $n$ put $c_d(0)=0$ and, for $n\ne0$,
$$c_d(n)=\prod_{p^k\parallel n}\bigl(\text{the coefficient of }T^k\text{ in }P_{d,p}(T)^{-1}\bigr),$$
with $P_{d,p}$ the [Euler polynomial](cd-euler-polynomial.md) of $C_d$ at $p$. The local factor
$P_{d,p}(T)^{-1}$ is $1$ at the primes $p\mid2d$ and $(1-a_pT+pT^2)^{-1}$ with
$a_p=p+1-\#C_d(\mathbb F_p)$ at the primes $p\nmid2d$; $c_d$ is built from these factors as the
coefficients of the formal Euler product $\prod_{p\nmid2d}(1-a_pp^{-s}+p^{1-2s})^{-1}$ are,
multiplicatively, with the coefficient of $T^k$ in the factor at $p$ placed at $p^k$.

1. If $d$ is odd and squarefree, then for every complex number $s$
   $$L(C_d,s)=\sum_{n\ge1}c_d(n)\,n^{-s},$$
   both sides read as in [entire continuations](../l-series-continuation.md): the sum of the series
   where it converges absolutely, and $0$ elsewhere.
2. The same holds for every squarefree $d$ with $d\equiv5\pmod8$.

This is an identity of series values, not of continuations. The literature statements use an
entire continuation, which is required to agree with these series only on
$\operatorname{Re}s>3/2$; for $\operatorname{Re}s\le3/2$, which contains the point $s=1$ where the
functional equation is used, nothing about the continuation is computed here.

For squarefree $d\equiv5\pmod8$, $L(C_d,s)$ is the L-series in the functional equation, in the
vanishing at the centre, in row 5b and in reading A. Hecke's continuation is stated for every
$d\ne0$ and Gross–Zagier for every elliptic curve over $\mathbb Q$; their L-series is not computed
here beyond odd squarefree $d$.

**Proof sketch.** (1) The two Dirichlet series have the same coefficient at every $n\ne0$, by
[every coefficient](coefficients.md) (2), so they agree at every $s$. (2) $d\equiv5\pmod8$ makes
$d$ odd; apply (1).

## Depends on

- [Entire continuations of the L-series of an elliptic curve](../l-series-continuation.md)
- [The Euler polynomial of $C_d$ at $p$](cd-euler-polynomial.md)

## Proof depends on

- [Every coefficient of $L(C_d,s)$](coefficients.md)

## Sources

- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
- [The L-series of an elliptic curve](../../../../sources/rank-locators.md#the-l-series-of-an-elliptic-curve)
