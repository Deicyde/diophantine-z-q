---
article_id: af_0d90618f18c521de6389829f
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Literature.isMultiplicative_LFunction, ZInQ.Literature.LFunction_cd_apply
---

# Every coefficient of $L(C_d,s)$

With $a_n(E)$ the coefficients of $L(E,s)$ as in
[the coefficients at prime powers](prime-power-coefficients.md):

1. For every Weierstrass equation $E$ over $\mathbb Q$, the function $n\mapsto a_n(E)$ is
   multiplicative: $a_1(E)=1$ and $a_{mn}(E)=a_m(E)a_n(E)$ for coprime $m$ and $n$.
2. If $d$ is odd and squarefree and $n\ne0$, then
   $$a_n(C_d)=\prod_{p^k\parallel n}\bigl(\text{the coefficient of }T^k\text{ in }P_{d,p}(T)^{-1}\bigr),$$
   the product over the primes $p$ dividing $n$, with $p^k$ the exact power of $p$ dividing $n$,
   and $P_{d,p}$ the [Euler polynomial](cd-euler-polynomial.md) of $C_d$ at $p$.

**Proof sketch.** (1) The factor at a place $v$ has coefficient $1$ at $1$ (the constant coefficient
of $f_v(T)^{-1}$ is $1$) and is supported on the powers of $q_v=p_v$, a prime, so it is
multiplicative; an Euler product of multiplicative factors is multiplicative. (2) Write $n$ as the
product of its prime powers; by (1) $a_n(C_d)$ is the product of the $a_{p^k}(C_d)$, each given by
[the coefficients at prime powers](prime-power-coefficients.md).

## Depends on

- [The coefficients of $L(C_d,s)$ at prime powers](prime-power-coefficients.md)
- [The Euler polynomial of $C_d$ at $p$](cd-euler-polynomial.md)

## Proof depends on

- [The places of $\mathbb Q$ and their completions](completion.md)

## Sources

- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
- [The L-series of an elliptic curve](../../../../sources/rank-locators.md#the-l-series-of-an-elliptic-curve)
