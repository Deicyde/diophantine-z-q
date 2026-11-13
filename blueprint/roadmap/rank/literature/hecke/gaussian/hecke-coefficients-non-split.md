---
article_id: af_4fae51cd3c41dd67776b0ae9
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.heckeCoeff_two_pow, ZInQ.Contrib.HeckeFE.heckeCoeff_pow_of_dvd, ZInQ.Contrib.HeckeFE.heckeCoeff_prime_of_dvd, ZInQ.Contrib.HeckeFE.heckeCoeff_inert
---

# The Hecke coefficients at the primes that do not split

Let $\lambda_d(n)$ be the [Hecke coefficients](hecke-coefficients.md).

1. For every natural number $d$ and every $m\ge1$, $\lambda_d(2^m)=0$.
2. If $d$ is odd, $p$ is a prime dividing $d$ and $m\ge1$, then $\lambda_d(p^m)=0$.
3. If $d$ is odd and squarefree and $p$ is a prime with $p\mid2d$, then $\lambda_d(p)=0$.
4. If $p\equiv3\pmod4$ is prime, $p\nmid d$ and $k\ge0$, then
   $\lambda_d(p^{k+2})=-p\,\lambda_d(p^k)$.

**Proof sketch.** (1) If $N(\alpha)=a^2+b^2$ is even, then $a+b$ is even and $u(\alpha)=0$
([primary unit](primary-unit.md) (3)), so every term vanishes.

(2) For $\alpha\in A_{p^m}$, $p^m$ and $d$ have the common factor $p$, so
$\left(\frac{N(\alpha)}d\right)=\left(\frac{p^m}d\right)=0$.

(3) By [Deuring's identity at the small primes](../deuring/deuring-small-primes.md) (5) and (6),
$\lambda_d(p)$ equals the coefficient $c_d(p)$ of $L(C_d,s)$ at $p$, which is $0$ for $p\mid2d$
([the coefficients at primes](../../l-function-cd/prime-coefficients.md)).

(4) By [norm fibres at primes](norm-fibres-primes.md) (2), $A_{p^{k+2}}=\{p\beta:\beta\in A_{p^k}\}$,
and $\beta\mapsto p\beta$ is injective. By the [Hecke character](hecke-character.md) (2),
$\psi_d(p\beta)=\psi_d(p)\psi_d(\beta)$, and $\psi_d(p)=\left(\frac{p^2}d\right)u(p)\,p=-p$: the
symbol is $1$ as $p\nmid d$, and $u(p)=u(3,0)=-1$ as $p\equiv3\pmod4$.

## Depends on

- [The coefficients of the Hecke L-series $L(\psi_d,s)$](hecke-coefficients.md)

## Proof depends on

- [The primary unit of a Gaussian integer modulo 4](primary-unit.md)
- [The Hecke character $\psi_d$](hecke-character.md)
- [Gaussian integers whose norm is a prime power](norm-fibres-primes.md)
- [Deuring's identity at the primes $2$, $p\mid d$ and $p\equiv3\pmod4$](../deuring/deuring-small-primes.md)
- [The coefficients of $L(C_d,s)$ at primes as point counts](../../l-function-cd/prime-coefficients.md)

## Sources

- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
