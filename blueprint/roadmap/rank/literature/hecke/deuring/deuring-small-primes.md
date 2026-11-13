---
article_id: af_2dc1ab7dd5bcbe0a8e959008
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.sum_quadraticChar_cd_eq_zero, ZInQ.Contrib.HeckeFE.card_cd_affine_of_mod_four_eq_three, ZInQ.Contrib.HeckeFE.cdCoeff_prime_of_mod_four_eq_three, ZInQ.Contrib.HeckeFE.deuring_prime_of_mod_four_eq_three, ZInQ.Contrib.HeckeFE.deuring_prime_of_dvd, ZInQ.Contrib.HeckeFE.deuring_two
---

# Deuring's identity at the primes $2$, $p\mid d$ and $p\equiv3\pmod4$

Let $c_d(n)$ be the coefficients of [the standard Euler product](../../l-function-cd/l-series.md),
$\lambda_d(n)$ the [Hecke coefficients](../gaussian/hecke-coefficients.md), and for a prime $p$ let
$\left(\frac{\cdot}{p}\right)$ be the quadratic character of $\mathbb F_p$ (with value $0$ at $0$).

1. If $p\equiv3\pmod4$ is prime and $d$ is a natural number, then
   $\sum_{x\in\mathbb F_p}\left(\frac{x^3-d^2x}p\right)=0$.
2. Under the same hypotheses, $\#\{(x,y)\in\mathbb F_p^2:y^2=x^3-d^2x\}=p$.
3. If $d$ is odd and squarefree, $p\equiv3\pmod4$ is prime and $p\nmid d$, then $c_d(p)=0$.
4. Under the hypotheses of (3), $c_d(p)=\lambda_d(p)$.
5. If $d$ is odd and squarefree and $p$ is a prime dividing $d$, then $c_d(p)=\lambda_d(p)$.
6. If $d$ is odd and squarefree, then $c_d(2)=\lambda_d(2)$.

**Proof sketch.** (1) The substitution $x\mapsto-x$ multiplies each term by
$\left(\frac{-1}p\right)=-1$, so the sum equals its negative.

(2) A value $x$ contributes $1+\left(\frac{x^3-d^2x}p\right)$ solutions $y$; sum over $x$ and use
(1).

(3) $p\nmid2d$, so $c_d(p)$ is $p$ minus the number of affine solutions
([deuring identity](deuring-identity.md) and
[the coefficients at primes](../../l-function-cd/prime-coefficients.md)), which is $0$ by (2).

(4) $A_p$ is empty since $p\equiv3\pmod4$
([norm fibres at primes](../gaussian/norm-fibres-primes.md) (1)), so $\lambda_d(p)=0$; and
$c_d(p)=0$ by (3).

(5) $c_d(p)=0$ since $p\mid2d$ (the coefficients at primes). For $\alpha\in A_p$,
$\left(\frac{N(\alpha)}d\right)=\left(\frac pd\right)=0$ since $p$ and $d$ have the common factor
$p$; so $\lambda_d(p)=0$.

(6) $c_d(2)=0$ since $2\mid2d$. For $\alpha=(a,b)\in A_2$,
$a^2+b^2\equiv2\pmod4$, and the table of the [primary unit](../gaussian/primary-unit.md) gives
$u(\alpha)=0$ for these residues; so $\lambda_d(2)=0$.

## Depends on

- [Deuring's identity for $C_d$](deuring-identity.md)
- [The coefficients of the Hecke L-series $L(\psi_d,s)$](../gaussian/hecke-coefficients.md)

## Proof depends on

- [The coefficients of $L(C_d,s)$ at primes as point counts](../../l-function-cd/prime-coefficients.md)
- [Gaussian integers whose norm is a prime power](../gaussian/norm-fibres-primes.md)
- [The primary unit of a Gaussian integer modulo 4](../gaussian/primary-unit.md)

## Sources

- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
- [The L-series of the congruent number curves](../../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
