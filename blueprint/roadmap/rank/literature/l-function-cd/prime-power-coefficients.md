---
article_id: af_7bee51f55a4c60cd04c942ec
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Literature.LFunction_cd_apply_prime_pow
---

# The coefficients of $L(C_d,s)$ at prime powers

For a Weierstrass equation $E$ over $\mathbb Q$, write $a_n(E)$ for the coefficients of the
Dirichlet series $L(E,s)=\sum_{n\ge1}a_n(E)n^{-s}$ of
[entire continuations](../l-series-continuation.md). They are the coefficients of the Euler product
over the finite places $v$ of $\mathbb Q$ in which the factor at $v$ is the series whose coefficient
at $q_v^k$ is the coefficient of $T^k$ in $f_v(T)^{-1}$, and whose other coefficients are $0$; here
$q_v=\#\kappa_v$ and $f_v$ is the [local polynomial](local-polynomial.md) of $E$ over
$\mathcal O_v$ (notation of [the places of $\mathbb Q$](completion.md)). For each $n$ the
coefficient at $n$ of the finite partial products is eventually constant, and $a_n(E)$ is that
value.

Let $d$ be an odd squarefree natural number, $p$ a prime and $k\ge0$. Then
$$a_{p^k}(C_d)=\text{the coefficient of }T^k\text{ in }P_{d,p}(T)^{-1},$$
where $P_{d,p}$ is the [Euler polynomial](cd-euler-polynomial.md) of $C_d$ at $p$ (its constant
coefficient is $1$, so it is invertible as a power series).

**Proof sketch.** By [the places of $\mathbb Q$](completion.md) (1) there is a finite place $v$ with
$p_v=p$. Every factor has coefficient $1$ at $1$, since the inverse series $f_w(T)^{-1}$ is formed
with constant coefficient $1$. For a place $w\ne v$, $q_w=p_w\ne p$ (the places of $\mathbb Q$ (1)
and (6)), and no divisor $m\ne1$ of $p^k$ is a power of $p_w$, so the factor at $w$ vanishes at
every such $m$. The partial products converge because for each bound only finitely many places have
$q_w$ below it (the places of $\mathbb Q$ (2)); take a finite set of places containing $v$ on which
the coefficient at $p^k$ has stabilized. The product of the factors at the other places of the set
has coefficient $1$ at $1$ and $0$ at every divisor $m\ne1$ of $p^k$, so the Dirichlet convolution
with it leaves the coefficient at $p^k$ of the factor at $v$ unchanged. That coefficient is the
coefficient of $T^k$ in $f_v(T)^{-1}$ (as $q_v=p$), and $f_v=P_{d,p}$ by [the local polynomial of
$C_d$](cd-local-polynomial.md) (3).

## Depends on

- [Entire continuations of the L-series of an elliptic curve](../l-series-continuation.md)
- [The Euler polynomial of $C_d$ at $p$](cd-euler-polynomial.md)
- [The local polynomial from any minimal equation](local-polynomial.md)
- [The places of $\mathbb Q$ and their completions](completion.md)

## Proof depends on

- [The local polynomial of $C_d$ at each prime](cd-local-polynomial.md)

## Sources

- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
- [The L-series of an elliptic curve](../../../../sources/rank-locators.md#the-l-series-of-an-elliptic-curve)
